(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: kept_run and same_io_wvb of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at
   5eaa5614305, awr_stk of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at fb6520a9cda, U_sext32_small of
   proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v at b0f706c04a1 and U_sx32_eqb of proofs/libreac/fuzz_knock/lib/A/APgStep.v
   at 6ebe35ba632, renamed (kept_run_pe, same_io_wvb_pe, pe_awr, pe_U_sx32, pe_U_sx32_eqb); pe_awr also reads sp's value
   through the token atoms a run adds; everything else below is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseE.v at afaa3cb55c1d; module paths and
   names changed to fuzz_rate's (RtPg* files, rt_fxk, Rate.parse_model, Rate.harness_parse, reac_rate_prop_parse), the
   .got cell 0x9be70 and the shadow-offset cell 0xa4c38 of fuzz_rate.asan in e1_entry, the comments' pcs and branch
   targets fuzz_rate.asan's. *)
(* reac_rate_prop_parse 0x8449c of reac-pw/fuzz_rate's ASan image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a): segments E1 and E2 of its walk, proving
   lib/A/RtPgParseBase.v's segE1_stmt and segE2_stmt on the concrete image rsegs.
   E1, 0x8449c .. H 0x844dc: the prologue stores ra, s0 .. s8 into [sp - 0x60, sp) (e1_stack); 0x844c8 beqz a0.
     NULL (a0 = 0, held as the literal): taken to 0x84894, a1 = -1, the epilogue 0x84898 .. 0x848c4 reloads the ten
     words, 0x848c8 ret: PPOST with (None, -1), nothing outside the frame written.
     non-NULL (a0 = P, atom 10 in [16, 2^47], 16-aligned): the engine decides the beqz; 0x844cc mv s0,a1;
     0x844d0 / 0x844d4 read the .got word at A_GOT_SH (e1_got: it holds A_SH_CELL), 0x844d8 the shadow-offset cell
     (e1_cell: SHADOW_OFF) into s3; at H the facts FI (the ten words from the stack region's chunks) and a0 = P give
     the cut H_at, and the hypothesis H_ok ends the walk.
   E2, H 0x844dc .. L1 0x84570: from H_at, env cut_env with slots 43 .. 45 the u32 at 0, 4, 8 of the pod, the frame
     region and the pod's first 16 bytes (16 <= len) or 8 bytes (len < 16) as a read-only region at atom 10 with
     the u32 as chunks, and the shadow entry of the same bytes (shent_pod). Branches, each split by the engine:
     0x844f4 bnez (S >> 20), 0x84510 bltu S, 8, 0x8451c bne type, 15, 0x84540 bne object type, 0x40002: ret -1, the
     model's VNotProps (parse_model_not_props); for len < 16, S = len - 8 < 8, so the run returns at 0x84510 and
     never reaches the check of P + 8. The 0x84548 bnez of (P + 8) & 3 is decided (P is 16-aligned).
     0x84550 bgeu S, 16: not taken, ret 0 (find_prop's first prop_is_inside fails: parse_model_no_params); taken,
     0x8455c .. 0x8456c set a4 = S - 16, a2 = P + 16, a5 = P + S - 8, a6 = 0x80001 and the run stops at L1, where
     L1_at x 16 holds (x_res from parse_model_found / _no_params, the fuel changed by Spa.find_prop_fuel) and the
     hypothesis L1_ok ends the walk. Every return leaf goes through e2_leaf_ok (leaf_regs, ppost_intro). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Model Spa Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require reac_rate_prop_parse.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import Img0 RtPgBase RtPgCSpec RtPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the plumbing ======================================= *)
Lemma same_io_wvb_pe : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a run keeps every byte outside the zone its write windows lie in [fuzz_role lib/A/RPgCfgChanges.v kept_run] *)
Lemma kept_run_pe : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
(* the write-range obligation: every writable region is based at sp (atom 2) and lies in the caller's stack
   allowance [fuzz_role lib/A/RPgCheck.v awr_stk]; B2 names sp's value *)
Ltac pe_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew _ 2) = ?spv |- _ =>
let B2' := fresh "B2'" in
assert (B2' : bv_unsigned (ew E 2) = spv) by (repeat rewrite ew_ewset_other by lia; exact B2);
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | rewrite B2'; lia | cbn [YP09.r_wlo YP09.r_whi]; unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia
| cbn [YP09.r_wlo YP09.r_whi]; unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia |] ]
end end.
(* every write window of a state lies in the callee's stack [sp - T_parse_STK, sp) *)
Ltac pe_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => repeat rewrite ew_ewset_other in Hb by lia; rewrite B2 in Hb end;
        unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia | lia ] | ]);
destruct Hr.
Ltac pe_run :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok parse_tbl_ok HS HJ SHOK RTBspan end.
Ltac pe_run_to stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok parse_tbl_ok HS HJ SHOK RTBspan stop end.
Ltac pe_keep :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (kept_run_pe _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by pe_kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac pe_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok parse_tbl_ok HS SH RTBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* a register at the stop, as the engine's symbolic value [fuzz_role lib/A/RPgCfgChanges.v cfg_r10] *)
Ltac pe_reg HS r Q :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Q : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS)
end.
Ltac pe_io := let rec kio := first [apply same_io_refl | assumption | eapply same_io_trans; [| apply same_io_wvb_pe]; kio] in kio.

(* ======================================= E1 ======================================= *)
(* the entry state: the prologue's ten stores go to [sp - 0x60, sp); the .got word at A_GOT_SH and the shadow-offset
   cell at A_SH_CELL are read-only regions with their values; sp in [2^46, 2^47]; a0 = 0 on the NULL path, a0 = P
   (in [16, 2^47], 16-aligned) else *)
Definition e1_stack : YP09.region := YP09.mkRegion (Some 2%nat) (- FRAME) 0 (- FRAME) 0 [].
Definition e1_got : YP09.region :=
YP09.mkRegion None A_GOT_SH (A_GOT_SH + 8) 0 0 [YP09.mkChunk A_GOT_SH (CVal 8 (SLit A_SH_CELL))].
Definition e1_cell : YP09.region :=
YP09.mkRegion None A_SH_CELL (A_SH_CELL + 8) 0 0 [YP09.mkChunk A_SH_CELL (CVal 8 (SLit SHADOW_OFF))].
Definition e1_regions : smem := [e1_stack; e1_got; e1_cell].
Definition e1_atoms (null : bool) : list (nat * afact) :=
(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (if null then [] else [(10%nat, mkAF 16 (2 ^ 47) 4)]).
Definition e1_sr (null : bool) : list sv := if null then sr_set sr_atoms (10%bv : bv 5) (SLit 0) else sr_atoms.
Definition ss_e1 (null : bool) : sstate := mkSS A_PARSE (e1_sr null) e1_regions None (mkFacts (e1_atoms null) [] []).
Definition e1_extra : list word := [Z_to_bv 64 SBr].
Definition E1Bx : sv := SOff 32 0.

(* ======================================= E2 ======================================= *)
(* the entry state at H: env cut_env x regs2 (e2_L x) (slots 43, 44, 45: the u32 at 0, 4, 8 of the pod), the frame
   region with no extra chunk, and the pod's first 16 bytes (big: 16 <= len) or 8 bytes as a read-only region at
   atom 10 (a0 = P) with those u32 as chunks; the shadow entry of the same bytes *)
Definition e2_pod (big : bool) : YP09.region :=
if big then YP09.mkRegion (Some 10%nat) 0 16 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 43 0)); YP09.mkChunk 4 (CVal 4 (SOff 44 0)); YP09.mkChunk 8 (CVal 4 (SOff 45 0))]
else YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 43 0)); YP09.mkChunk 4 (CVal 4 (SOff 44 0))].
Definition e2_regions (big : bool) : smem := [frame_region []; e2_pod big].
Definition e2_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 16 (2 ^ 47 - 16) 4); (19%nat, mkAF SBr SBr 0);
  (43%nat, mkAF 0 (2 ^ 32 - 1) 0); (44%nat, mkAF 0 (2 ^ 32 - 1) 0); (45%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_e2 (big : bool) : sstate := mkSS PC_H sr_atoms (e2_regions big) None e2_facts.
Definition e2_SH (big : bool) : list shent := [mkSHE 10 0 (if big then 16 else 8)].
Definition e2_L (x : pctx) : list word :=
[w64 (Spa.u32_at (x_bs x) 0); w64 (Spa.u32_at (x_bs x) 4); w64 (Spa.u32_at (x_bs x) 8)].

(* ---- the values of E2's header tests, over the engine's symbolic values ---- *)
(* `lw` of a field below 2^31 sign-extends to itself [fuzz_qdisc lib/A/QPgLoop0.v U_sext32_small] *)
Lemma pe_U_sx32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia.
rewrite (Z.mod_small v (2 ^ Z.of_N 32)) by (change (2 ^ Z.of_N 32) with (2 ^ 32); lia).
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
apply zcanon_id. unfold M64. lia.
Qed.
(* its low 32 bits are the field *)
Lemma pe_U_sx32_mod : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 (SOff n 0)) mod 2 ^ 32 = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec v (2 ^ 31)).
- rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
  rewrite !Z.mod_small by lia. reflexivity.
- replace (v + 2 ^ 31) with ((v - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v - 2 ^ 31) (2 ^ 32)) by lia.
  replace (v - 2 ^ 31 - 2 ^ 31) with ((v - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (v - 2 ^ 32 + 2 ^ 64) (2 ^ 64)) by lia.
  replace (v - 2 ^ 32 + 2 ^ 64) with (v + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.
(* `srliw 20` of the sign-extended field: the field divided by 2^20 *)
Lemma pe_U_srliw20 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
U E (SAluw ALU_SRL (SExt true 32 (SOff n 0)) (SLit 20)) = v / 2 ^ 20.
Proof.
intros E n v Hn Hv. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (pe_U_sx32_mod E n v Hn Hv), U_SLit. change (zcanon 20 mod 2 ^ 32) with 20. change (Z.land 20 31) with 20.
rewrite Z.shiftr_div_pow2 by lia.
assert (0 <= v / 2 ^ 20 < 2 ^ 12) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
(* the compare of a sign-extended field with a small literal [knock lib/A/APgStep.v U_sx32_eqb] *)
Lemma pe_U_sx32_eqb : forall E n s c, ew E n = Z_to_bv 64 s -> 0 <= s < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
(U E (SExt true 32 (SOff n 0)) =? U E (SLit c)) = (s =? c).
Proof.
intros E n s c Hn Hs Hc. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n s Hn) by lia. rewrite U_lit by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
destruct (Z.ltb_spec s (2 ^ 31)).
- rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia. rewrite Z.mod_small by lia. reflexivity.
- replace (s + 2 ^ 31) with ((s - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (s - 2 ^ 31)) by lia.
  replace (s - 2 ^ 31 - 2 ^ 31) with ((s + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  destruct (Z.eqb_spec (s + (2 ^ 64 - 2 ^ 32)) c); destruct (Z.eqb_spec s c); first [reflexivity | lia].
Qed.

(* sums the find loop's registers hold at L1 *)
Lemma pe_U_add_lit : forall E a v c, U E a = v -> 0 <= v + c < 2 ^ 64 -> - 2 ^ 64 < c < 2 ^ 64 ->
U E (SAlu ALU_ADD a (SLit c)) = v + c.
Proof.
intros E a v c Ha Hv Hc. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit. unfold zcanon, M64.
rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. lia.
Qed.
Lemma pe_U_add2 : forall E a b u v, U E a = u -> U E b = v -> 0 <= u + v < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = u + v.
Proof. intros E a b u v Ha Hb Huv. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. apply zcanon_id. unfold M64. lia. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HGOT : as_got_shadow B = A_GOT_SH.
Hypothesis HCELL : as_shadow_cell B = A_SH_CELL.

Lemma e1_entry : forall x null, call_ok B x null ->
st_ok rsegs (Ereg (x_regs x) e1_extra) (ss_e1 null)
(restrict (w_H (x_W x)) (mkst (x_regs x) (Z_to_bv 64 A_PARSE) (x_memc x) (seg_rom rsegs))).
Proof.
intros x null Hc.
destruct Hc as ((HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) & H10 & H11 & Hpod & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HGOT, HCELL in Kgot. rewrite HCELL in Kcell.
unfold T_parse_STK, ESTACK in Hwlo.
rewrite restrict_mkst_fx.
set (E := Ereg (x_regs x) e1_extra).
assert (Usp : bv_unsigned (ew E 2) = spZ (x_regs x)) by (subst E; rewrite (ew_Ereg_nat (x_regs x) _ 2 2%bv eq_refl); reflexivity).
unfold ss_e1. apply (entry_st_ok_full rsegs); change (Ereg (x_regs x) e1_extra) with E.
- destruct null; unfold e1_sr; [|apply regs_ok_Ereg].
  apply regs_ok_pin; [apply regs_ok_Ereg | |].
  + intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz.
  + rewrite H10. reflexivity.
- vm_compute. reflexivity.
- unfold e1_regions, e1_stack, e1_got, e1_cell. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. unfold FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
  + unfold A_GOT_SH. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 0x9be70 8 (SLit A_SH_CELL) A_SH_CELL); [reflexivity | unfold A_SH_CELL; zside | zside |].
    rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs _ _ _ _ Kgot).
  + unfold A_SH_CELL. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 0xa4c38 8 (SLit SHADOW_OFF) SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold e1_regions, e1_stack, e1_got, e1_cell, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_GOT_SH, A_SH_CELL, FRAME.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  destruct null; cbn [e1_atoms f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?Usp;
  change (2 ^ 4) with 16.
  + repeat split; lia.
  + destruct (Hpod eq_refl) as (HP0 & HP16 & Hl8 & _ & _ & _ & _ & _ & HAM & _).
    pose proof (amem_range_bounds (x_P x) (x_len x) ltac:(lia) ltac:(lia) HAM) as Hhm.
    assert (U10 : bv_unsigned (ew E 10) = x_P x).
    { subst E. rewrite (ew_Ereg_nat (x_regs x) _ 10 10%bv eq_refl), H10. apply unsigned_lit_small. lia. }
    rewrite U10. repeat split; lia.
Qed.

Lemma segE1_ok : segE1_stmt B MT.
Proof using MTL LAWS HGOT HCELL.
unfold segE1_stmt. intros x null Hc HH.
pose proof (e1_entry x null Hc) as HS.
destruct Hc as ((HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) & H10 & H11 & Hpod & _ & _ & _ & _ & _ & Hfrm).
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
remember (Ereg (x_regs x) e1_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg (x_regs x) e1_extra) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr (x_regs x) 1) by (subst E; exact (ew_Ereg_nat (x_regs x) _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ (x_regs x)) by (subst E; rewrite (ew_Ereg_nat (x_regs x) _ 2 2%bv eq_refl); reflexivity).
assert (EA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (x_regs x) r)
by (intros n r Hn; subst E; exact (ew_Ereg_nat (x_regs x) _ n r Hn)).
clear HE.
assert (SHOK : sh_ok rsegs E1Bx [] E (mrestrict (w_H (x_W x)) (x_memc x))) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
  aview rsegs (w_H (x_W x)) (x_memc x) a = aview rsegs (w_H (x_W x)) (x_memc x) a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_PARSE) with (Z_to_bv 64 A_PARSE).
destruct null.
- (* NULL: 0x844c8 beqz a0 taken, 0x84894 a1 = -1, the epilogue 0x84898 .. 0x848c4, stop at 0x848c8 ret *)
  pe_run; [pe_awr | ].
  pe_keep.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
    rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10;
    eapply (SRr_ret_at rsegs parse_tbl parse_tbl_ok parse_wx (x_W x) E); [exact HS | reflexivity | vm_compute; reflexivity |]
  end.
  intros mat'.
  replace (v_jalr (getr (ms_regs ms) 1) 0) with (getr (x_regs x) 1) by (rewrite R1, E1, Hra; reflexivity).
  apply (ppost_intro B MT MTL x true fx).
  + eapply ajournal_materialize; eassumption.
  + pe_io.
  + eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity].
  + apply rt_fxk_refl. exact Hfrm.
  + intros a Ha Hz _. exact (KE a Ha Hz).
  + rewrite R10. unfold Rate.harness_parse. cbn [snd]. apply bv_eq. vm_compute. reflexivity.
  + exact I.
- (* non-NULL: the beqz is decided not taken (atom 10 in [16, 2^47]); 0x844cc .. 0x844d8, stop at H 0x844dc *)
  pe_run_to PC_H; [pe_awr | ].
  pe_keep.
  lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
    pose proof (st_ok_restrict_mkst rsegs (w_H (x_W x)) E ss ms HS eq_refl) as Hshape;
    rreg HS (2%bv : bv 5) R2; rreg HS (8%bv : bv 5) R8; rreg HS (19%bv : bv 5) R19; rreg HS (10%bv : bv 5) R10
  end.
  rewrite Hshape.
  lazymatch goal with |- SRr ?s ?W (mkCfg (mkst ?rg _ ?mm _) ?md) ?Q => change (SRr s W (cfg_at rsegs PC_H rg mm md) Q) end.
  apply (HH eq_refl).
  unfold H_at, FI.
  split; [|rewrite R10, (EA 10%nat 10%bv eq_refl), H10; reflexivity].
  split; [exact HJ|].
  split; [pe_io|].
  split; [exact KE|].
  split.
  { (* the ten saved words: the stack region's chunks at sp - 0x50 .. sp - 8 *)
    lazymatch goal with HS : st_ok _ _ _ _ |- _ => pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HRs & _) end.
    cbn [ss_mem ms_mem restrict] in HRs.
    apply Forall_cons_iff in HRs as [HR0 _].
    unfold region_ok in HR0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR0.
    rewrite B2 in HR0. destruct HR0 as (_ & _ & _ & HCs).
    repeat (let Hc1 := fresh "HCk" in apply Forall_cons_iff in HCs; destruct HCs as [Hc1 HCs]).
    unfold SAVED. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    lazymatch goal with |- val_mem _ ?m (x_F x + ?off) 8 (bv_unsigned (getr (x_regs x) (Z_to_bv 5 ?r))) =>
      let o := eval vm_compute in (off - 96) in
      let n := eval vm_compute in (Z.to_nat r) in
      lazymatch goal with Hc : YP09.chunk_ok _ _ _ _ (YP09.mkChunk o (CVal 8 (SOff n 0))) |- _ =>
        replace (x_F x + off) with (spZ (x_regs x) + o) by (unfold x_F, x_sp, FRAME; lia);
        apply (val_of_chunk_ok rsegs E m _ o 8 (SOff n 0) _ Hc);
        [ rewrite sv_denot_SOff0, (EA n (Z_to_bv 5 r) eq_refl); symmetry; apply Z_to_bv_bv_unsigned
        | apply bv_unsigned_in_range | lia ]
      end
    end. }
  split; [rewrite R2, B2; unfold x_F, x_sp, FRAME, w64; f_equal; lia|].
  split.
  { intros r Hr.
    lazymatch goal with HS : st_ok _ _ ?ss (restrict ?Hh ?ms) |- _ =>
      pose proof (regs_kept_of_st_ok rsegs E ss (restrict Hh ms) (x_regs x) e1_extra
        [Z_to_bv 5 3; Z_to_bv 5 4; Z_to_bv 5 25; Z_to_bv 5 26; Z_to_bv 5 27] HS HAE ltac:(vm_compute; reflexivity)) as HK
    end.
    cbn [ms_regs restrict] in HK.
    destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; apply HK; repeat (first [left; reflexivity | right]). }
  split; [rewrite R8, (EA 11%nat 11%bv eq_refl), H11; reflexivity|].
  rewrite R19. reflexivity.
Qed.

Lemma e2_entry : forall x regs2 mem2 md2 (big : bool), pre_ok B x -> FI B x regs2 mem2 md2 ->
getr regs2 10 = w64 (x_P x) -> (big = true -> 16 <= x_len x) ->
st_ok rsegs (cut_env x regs2 (e2_L x)) (ss_e2 big)
  (restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_H) mem2 (seg_rom rsegs))) /\
sh_ok rsegs PBx (e2_SH big) (cut_env x regs2 (e2_L x)) (mrestrict (w_H (x_W x)) mem2).
Proof.
intros x regs2 mem2 md2 big Hpre HFI H10 Hbig.
pose proof (pre_pod B x Hpre) as (HP0 & HP16 & Hl8 & HSZ & HP63 & _ & _ & _ & HAM & HDJ).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof (amem_range_bounds (x_P x) (x_len x) ltac:(lia) ltac:(lia) HAM) as Hhm.
pose proof (pod_at_cut B x regs2 mem2 md2 Hpre HFI) as (HG & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HFI as (HJ & Hio & HK & HSV & H2 & Hcs & H8 & H19).
set (E := cut_env x regs2 (e2_L x)).
assert (E2 : ew E 2 = getr regs2 2) by (apply cut_env_reg; reflexivity).
assert (E10 : ew E 10 = getr regs2 10) by (apply cut_env_reg; reflexivity).
assert (E19 : ew E 19 = getr regs2 19) by (apply cut_env_reg; reflexivity).
assert (E43 : ew E 43 = w64 (Spa.u32_at (x_bs x) 0)) by exact (cut_env_seg x regs2 (e2_L x) 0).
assert (E44 : ew E 44 = w64 (Spa.u32_at (x_bs x) 4)) by exact (cut_env_seg x regs2 (e2_L x) 1).
assert (E45 : ew E 45 = w64 (Spa.u32_at (x_bs x) 8)) by exact (cut_env_seg x regs2 (e2_L x) 2).
pose proof (u32_at_range (x_bs x) 0) as R0. pose proof (u32_at_range (x_bs x) 4) as R4.
pose proof (u32_at_range (x_bs x) 8) as R8.
assert (UF : bv_unsigned (ew E 2) = x_F x)
by (rewrite E2, H2; apply unsigned_lit_small; unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia).
assert (UP : bv_unsigned (ew E 10) = x_P x) by (rewrite E10, H10; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = SBr) by (rewrite E19, H19; reflexivity).
assert (U43 : bv_unsigned (ew E 43) = Spa.u32_at (x_bs x) 0) by (rewrite E43; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E 44) = Spa.u32_at (x_bs x) 4) by (rewrite E44; apply unsigned_lit_small; lia).
assert (U45 : bv_unsigned (ew E 45) = Spa.u32_at (x_bs x) 8) by (rewrite E45; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_e2.
  change E with (Ereg regs2 (w64 SBr :: saved_vals (x_regs x) ++ e2_L x)).
  apply (entry_st_ok_full rsegs); change (Ereg regs2 (w64 SBr :: saved_vals (x_regs x) ++ e2_L x)) with E.
  + apply regs_ok_Ereg.
  + destruct big; vm_compute; reflexivity.
  + unfold e2_regions. apply Forall_cons; [exact (frame_region_ok B x regs2 mem2 md2 (e2_L x) [] HFI Hpre (Forall_nil _))|].
    apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, e2_pod. destruct big;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite UP;
    (split; [lia|]); (split; [specialize (Hbig eq_refl) || idtac; lia|]); (split; [intros o Ho; lia|]);
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 4 (SOff ?n 0))) =>
      apply (chunk_ok_val rsegs E _ (x_P x) off 4 (SOff n 0) (Spa.u32_at (x_bs x) off));
      [ rewrite sv_denot_SOff0; first [rewrite E43 | rewrite E44 | rewrite E45]; reflexivity
      | apply u32_at_range | lia | apply pod_u32; [exact HG | lia | first [specialize (Hbig eq_refl) | idtac]; lia] ]
    end.
  + apply pairwise_disjoint_of_extents. unfold e2_regions, frame_region, e2_pod, extent_of_region.
    destruct big; cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; cbn [base_val]; rewrite UF, UP;
    cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
    unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; first [specialize (Hbig eq_refl) | idtac];
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    unfold e2_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UF, UP, U19, U43, U44, U45. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK, SBr in *. repeat split; lia.
- unfold sh_ok, e2_SH. constructor; [|constructor].
  apply (shent_pod B x regs2 mem2 md2 E PBx 10 0 0 (if big then 16 else 8) Hpre HFI).
  + unfold PBx. apply U_atom; [rewrite E19, H19; reflexivity | unfold SHADOW_OFF; lia].
  + rewrite Z.add_0_r. apply U_atom; [rewrite E10, H10; reflexivity | lia].
  + lia.
  + destruct big; [specialize (Hbig eq_refl)|]; lia.
  + destruct big; lia.
Qed.

(* the leaf of a return in E2 (or after): leaf_regs for the registers, ppost_intro for the post *)
Lemma e2_leaf_ok : forall x regs2 L E' ss ms md,
pre_ok B x ->
getr regs2 2 = w64 (x_F x) ->
(forall r, r = 3 \/ r = 4 \/ r = 25 \/ r = 26 \/ r = 27 -> getr regs2 (Z_to_bv 5 r) = getr (x_regs x) (Z_to_bv 5 r)) ->
st_ok rsegs E' ss (restrict (w_H (x_W x)) ms) -> ss_resv ss = None -> clookup parse_tbl (ss_pc ss) = Some RET_WORD_r ->
(forall n, (n < 43)%nat -> ew E' n = ew (cut_env x regs2 L) n) -> leaf_sr_ok (ss_regs ss) = true ->
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
  (x_lyc x) (x_Sc x) (x_W x) (ms_mem ms) md (x_k x) ->
same_io (x_mdc x) md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
  aview rsegs (w_H (x_W x)) (ms_mem ms) a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
getr (ms_regs ms) 10 = w64 (snd (Rate.parse_model (x_bs x))) -> fst (Rate.parse_model (x_bs x)) = None ->
SRr rsegs (x_W x) (mkCfg ms md) (PPOST B MT x false).
Proof using MTL LAWS.
intros x regs2 L E' ss ms md Hpre H2 Hcs HS Hrv Hret HE Hok HJ Hio KE H10 Hn.
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
destruct (leaf_regs B x regs2 L E' ss ms (w_H (x_W x)) Hpre HS HE Hok H2 Hcs) as [Hpr H1].
pose proof Hpre as ((_ & Hra & _) & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm).
eapply (SRr_ret_at rsegs parse_tbl parse_tbl_ok parse_wx (x_W x) E'); [exact HS | exact Hrv | exact Hret |].
intros mat.
replace (v_jalr (getr (ms_regs ms) 1) 0) with (getr (x_regs x) 1) by (rewrite H1, Hra; reflexivity).
apply (ppost_intro B MT MTL x false fx).
- eapply ajournal_materialize; eassumption.
- eapply same_io_trans; [exact Hio | apply same_io_wvb_pe].
- exact Hpr.
- apply rt_fxk_refl. exact Hfrm.
- intros a Ha Hz _. exact (KE a Ha Hz).
- exact H10.
- change (Rate.harness_parse false (x_bs x)) with (Rate.parse_model (x_bs x)). rewrite Hn. exact I.
Qed.
(* a return leaf of a segment that starts at a cut: e2_leaf_ok with a0 from the state and the model's answer Hres *)
Ltac e2_leafT Hpre H2 Hcs HE Hres :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
let R10 := fresh "R10" in rreg HS (10%bv : bv 5) R10;
eapply e2_leaf_ok;
[ exact Hpre | exact H2 | exact Hcs | exact HS | reflexivity | vm_compute; reflexivity
| intros n Hn; repeat rewrite ew_ewset_other by lia; rewrite HE; reflexivity | vm_compute; reflexivity | eassumption | pe_io | eassumption
| rewrite R10, Hres; apply bv_eq; vm_compute; reflexivity | rewrite Hres; reflexivity ] end.

Lemma segE2_ok : segE2_stmt B MT.
Proof using MTL LAWS.
unfold segE2_stmt, H_ok. intros x Hpre HL1 regs2 mem2 md2 (HFI & H10).
pose proof (pre_pod B x Hpre) as (HP0 & HP16 & Hl8 & HSZ & HP63 & _ & _ & _ & HAM & HDJ).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof (u32_at_range (x_bs x) 0) as R0. pose proof (u32_at_range (x_bs x) 4) as R4.
pose proof (u32_at_range (x_bs x) 8) as R8.
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
pose proof HFI as (HJ & Hio & KE & HSV & H2 & Hcs & H8 & H19).
unfold x_SZ in HSZ. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (Z_lt_le_dec (x_len x) 16) as [Hsmall | Hbig].
- (* len < 16, so S = len - 8 < 8: the shadow entry covers the 8 bytes the run reads before the S < 8 return *)
  destruct (e2_entry x regs2 mem2 md2 false Hpre HFI H10 (fun Hf => ltac:(discriminate Hf))) as [HS SHOK].
  remember (cut_env x regs2 (e2_L x)) as E eqn:HE.
  assert (B2 : bv_unsigned (ew E 2) = x_F x)
  by (rewrite HE, (cut_env_reg x regs2 _ 2 2%bv eq_refl), H2; apply unsigned_lit_small;
      unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia).
  assert (E43 : ew E 43 = w64 (Spa.u32_at (x_bs x) 0)) by (rewrite HE; exact (cut_env_seg x regs2 (e2_L x) 0)).
  unfold cfg_at. change (w64 PC_H) with (Z_to_bv 64 PC_H).
  (* 0x844dc .. 0x844f0; stop at 0x844f4 bnez (S >> 20): S < 8, not taken *)
  pe_run; [pe_awr|]. pe_keep.
  pe_branch Hc1; rewrite branch_ne_U, (pe_U_srliw20 E 43 _ E43 R0), U_lit in Hc1 by lia.
  { apply negb_true_iff, Z.eqb_neq in Hc1. exfalso. apply Hc1. apply Z.div_small. lia. }
  pose proof (pe_U_sx32 E 43 _ E43 ltac:(lia)) as US.
  (* 0x844f8 .. 0x8450c; stop at 0x84510 bltu S, 8: taken *)
  pe_run; [pe_awr|]. pe_keep.
  lazymatch goal with HS : st_ok _ ?E' _ _ |- _ =>
    assert (E43' : ew E' 43 = w64 (Spa.u32_at (x_bs x) 0)) by (repeat rewrite ew_ewset_other by lia; exact E43) end.
  pose proof (pe_U_sx32 _ 43 _ E43' ltac:(lia)) as US'.
  pe_branch Hc2; rewrite branch_ltu_U, US', U_lit in Hc2 by lia.
  2:{ apply Z.ltb_ge in Hc2. exfalso. lia. }
  assert (Hres : Rate.parse_model (x_bs x) = (None, -1)).
  { apply reac_rate_prop_parse.parse_model_not_props. unfold Spa.is_object_type.
    rewrite (proj2 (Z.leb_gt 8 _)) by lia. rewrite andb_false_r. reflexivity. }
  pe_run; [pe_awr|]. pe_keep. e2_leafT Hpre H2 Hcs HE Hres.
- destruct (e2_entry x regs2 mem2 md2 true Hpre HFI H10 (fun _ => Hbig)) as [HS SHOK].
  remember (cut_env x regs2 (e2_L x)) as E eqn:HE.
  assert (B2 : bv_unsigned (ew E 2) = x_F x)
  by (rewrite HE, (cut_env_reg x regs2 _ 2 2%bv eq_refl), H2; apply unsigned_lit_small;
      unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia).
  assert (E43 : ew E 43 = w64 (Spa.u32_at (x_bs x) 0)) by (rewrite HE; exact (cut_env_seg x regs2 (e2_L x) 0)).
  assert (E44 : ew E 44 = w64 (Spa.u32_at (x_bs x) 4)) by (rewrite HE; exact (cut_env_seg x regs2 (e2_L x) 1)).
  assert (E45 : ew E 45 = w64 (Spa.u32_at (x_bs x) 8)) by (rewrite HE; exact (cut_env_seg x regs2 (e2_L x) 2)).
  unfold cfg_at. change (w64 PC_H) with (Z_to_bv 64 PC_H).
  (* 0x844dc .. 0x844f0: the check of P, lw S, srliw; stop at 0x844f4 bnez *)
  pe_run; [pe_awr|]. pe_keep.
  pe_branch Hc1; rewrite branch_ne_U, (pe_U_srliw20 E 43 _ E43 R0), U_lit in Hc1 by lia.
  + (* S >= 2^20: ret -1 *)
    apply negb_true_iff, Z.eqb_neq in Hc1.
    assert (Hres : Rate.parse_model (x_bs x) = (None, -1)).
    { apply reac_rate_prop_parse.parse_model_not_props. unfold Spa.is_object_type, Spa.SPA_POD_MAX_SIZE.
      rewrite (proj2 (Z.ltb_ge _ _)); [reflexivity|].
      destruct (Z_lt_le_dec (Spa.u32_at (x_bs x) 0) (2 ^ 20)); [|lia]. exfalso. apply Hc1. apply Z.div_small. lia. }
    pe_run; [pe_awr|]. pe_keep. e2_leafT Hpre H2 Hcs HE Hres.
  + apply negb_false_iff, Z.eqb_eq in Hc1.
    assert (HS20 : Spa.u32_at (x_bs x) 0 < 2 ^ 20).
    { destruct (Z_lt_le_dec (Spa.u32_at (x_bs x) 0) (2 ^ 20)) as [|Hge]; [assumption|].
      exfalso. pose proof (Z.div_le_mono (2 ^ 20) _ (2 ^ 20) ltac:(lia) Hge) as Hd. rewrite Z.div_same in Hd by lia. lia. }
    pose proof (pe_U_sx32 E 43 _ E43 ltac:(lia)) as US.
    (* 0x844f8 .. 0x8450c: the check of P + 4; stop at 0x84510 bltu S, 8 *)
    pe_run; [pe_awr|]. pe_keep.
    pe_branch Hc2; rewrite branch_ltu_U, US, U_lit in Hc2 by lia.
    * (* S < 8: ret -1 *)
      apply Z.ltb_lt in Hc2.
      assert (Hres : Rate.parse_model (x_bs x) = (None, -1)).
      { apply reac_rate_prop_parse.parse_model_not_props. unfold Spa.is_object_type.
        rewrite (proj2 (Z.leb_gt 8 _)) by lia. rewrite andb_false_r. reflexivity. }
      pe_run; [pe_awr|]. pe_keep. e2_leafT Hpre H2 Hcs HE Hres.
    * apply Z.ltb_ge in Hc2.
      (* 0x84514 lw the type; stop at 0x8451c bne type, 15 *)
      pe_run; [pe_awr|]. pe_keep.
      pe_branch Hc3; rewrite branch_ne_U, (pe_U_sx32_eqb E 44 _ 15 E44 R4) in Hc3 by lia.
      -- (* the type is not Object: ret -1 *)
         apply negb_true_iff, Z.eqb_neq in Hc3.
         assert (Hres : Rate.parse_model (x_bs x) = (None, -1)).
         { apply reac_rate_prop_parse.parse_model_not_props. unfold Spa.is_object_type.
           rewrite (proj2 (Z.eqb_neq _ Model.POD_OBJECT)) by (unfold Model.POD_OBJECT; exact Hc3).
           rewrite andb_false_r. reflexivity. }
         pe_run; [pe_awr|]. pe_keep. e2_leafT Hpre H2 Hcs HE Hres.
      -- apply negb_false_iff, Z.eqb_eq in Hc3.
         (* 0x84520 .. 0x8453c: the check of P + 8, lw the object type; stop at 0x84540 bne *)
         pe_run; [pe_awr|]. pe_keep.
         pe_branch Hc4; rewrite branch_ne_U, (pe_U_sx32_eqb E 45 _ 262146 E45 R8) in Hc4 by lia.
         ++ (* not a Props object: ret -1 *)
            apply negb_true_iff, Z.eqb_neq in Hc4.
            assert (Hres : Rate.parse_model (x_bs x) = (None, -1)).
            { apply reac_rate_prop_parse.parse_model_not_props. unfold Spa.is_object_type.
              rewrite (proj2 (Z.eqb_neq _ Model.POD_OBJECT_PROPS)) by (unfold Model.POD_OBJECT_PROPS; exact Hc4).
              rewrite andb_false_r. reflexivity. }
            pe_run; [pe_awr|]. pe_keep. e2_leafT Hpre H2 Hcs HE Hres.
         ++ apply negb_false_iff, Z.eqb_eq in Hc4.
            assert (Hobj : Spa.is_object_type (x_bs x) Model.POD_OBJECT_PROPS = true).
            { unfold Spa.is_object_type, Spa.SPA_POD_MAX_SIZE, Model.POD_OBJECT, Model.POD_OBJECT_PROPS.
              rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by exact Hc3.
              rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by exact Hc4. reflexivity. }
            (* 0x84544 andi / bnez (P + 8 is 4-aligned: decided); stop at 0x84550 bgeu S, 16 *)
            pe_run; [pe_awr|]. pe_keep.
            pe_branch Hc5; rewrite branch_geu_U, US, U_lit in Hc5 by lia.
            ** (* S >= 16: 0x8455c .. 0x8456c, stop at L1 *)
               apply negb_true_iff, Z.ltb_ge in Hc5.
               pe_run_to PC_L1; [pe_awr|]. pe_keep.
               assert (E10 : ew E 10 = Z_to_bv 64 (x_P x)) by (rewrite HE, (cut_env_reg x regs2 _ 10 10%bv eq_refl), H10; reflexivity).
               assert (HAE : env_agree 32 (Ereg regs2 (w64 SBr :: saved_vals (x_regs x) ++ e2_L x)) E)
               by (rewrite HE; unfold cut_env; apply env_agree_refl).
               lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
                 pose proof (st_ok_restrict_mkst rsegs (w_H (x_W x)) E ss ms HS eq_refl) as Hshape;
                 pe_reg HS (2%bv : bv 5) Q2; pe_reg HS (8%bv : bv 5) Q8; pe_reg HS (19%bv : bv 5) Q19;
                 pe_reg HS (10%bv : bv 5) Q10; pe_reg HS (12%bv : bv 5) Q12; pe_reg HS (14%bv : bv 5) Q14;
                 pe_reg HS (15%bv : bv 5) Q15; pe_reg HS (16%bv : bv 5) Q16;
                 pose proof (regs_kept_of_st_ok rsegs E ss (restrict (w_H (x_W x)) ms) regs2 _
                   [Z_to_bv 5 3; Z_to_bv 5 4; Z_to_bv 5 25; Z_to_bv 5 26; Z_to_bv 5 27] HS HAE ltac:(vm_compute; reflexivity)) as HK
               end.
               cbn [ms_regs restrict] in HK.
               rewrite Hshape.
               lazymatch goal with |- SRr ?s ?W (mkCfg (mkst ?rg _ ?mm _) ?md) ?Q =>
                 change (SRr s W (cfg_at rsegs PC_L1 rg mm md) Q) end.
               apply (HL1 16).
               assert (USm : U E (SAlu ALU_ADD (SExt true 32 (SOff 43 0)) (SLit (-16))) = Spa.u32_at (x_bs x) 0 - 16)
               by (apply pe_U_add_lit; [exact US | lia | lia]).
               unfold L1_at, FI.
               split; [split; [eassumption|]|].
               { split; [pe_io|]. split; [exact KE|]. split.
                 - (* the saved words: the frame region's chunks *)
                   lazymatch goal with HS : st_ok _ _ _ _ |- _ => pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HRs & _) end.
                   cbn [ss_mem ms_mem restrict] in HRs. apply Forall_cons_iff in HRs as [HR0 _].
                   apply (saved_of_frame_region x E _ [] HR0); [cbn [base_val]; exact B2|].
                   intros j Hj. rewrite HE. apply cut_env_saved. exact Hj.
                 - split; [rewrite Q2, sv_denot_SOff0, HE, (cut_env_reg x regs2 _ 2 2%bv eq_refl); exact H2|].
                   split; [intros r Hr; rewrite <- (Hcs r Hr); apply HK;
                     destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; repeat (first [left; reflexivity | right])|].
                   split; [rewrite Q8, sv_denot_SOff0, HE, (cut_env_reg x regs2 _ 8 8%bv eq_refl); exact H8|].
                   rewrite Q19, sv_denot_SOff0, HE, (cut_env_reg x regs2 _ 19 19%bv eq_refl); exact H19. }
               split; [rewrite Q10, denot_lit_U, (U_atom_off E 10 (x_P x) 8 E10) by lia; reflexivity|].
               split; [rewrite Q12, denot_lit_U, (U_atom_off E 10 (x_P x) 16 E10) by lia; reflexivity|].
               split; [rewrite Q14, denot_lit_U, USm; reflexivity|].
               split; [rewrite Q15, denot_lit_U, (pe_U_add2 E _ _ _ _ USm (U_atom_off E 10 (x_P x) 8 E10 ltac:(lia) ltac:(lia))) by lia;
                 unfold w64, x_SZ; f_equal; lia|].
               split; [rewrite Q16; reflexivity|].
               split; [exact Hobj|].
               split; [unfold x_SZ; lia|].
               split; [unfold x_len in *; lia|].
               split; [reflexivity|].
               (* the model: parse_model from find_prop at 16, with the canonical fuel *)
               unfold x_res, x_SZ.
               rewrite (Spa.find_prop_fuel (x_bs x) (Spa.u32_at (x_bs x) 0) Model.POD_PROP_PARAMS 16
                 (S (Z.to_nat (8 + Spa.u32_at (x_bs x) 0 - 16))) (length (x_bs x))) by (unfold x_len in *; lia).
               destruct (Spa.find_prop (x_bs x) (Spa.u32_at (x_bs x) 0) Model.POD_PROP_PARAMS 16 (length (x_bs x)))
                 as [r|] eqn:EF.
               --- rewrite (reac_rate_prop_parse.parse_model_found _ r Hobj EF). reflexivity.
               --- rewrite (reac_rate_prop_parse.parse_model_no_params _ Hobj EF). reflexivity.
            ** (* S < 16: 0x84554 a1 = 0, j 0x84898, the epilogue, ret 0: find_prop's first test fails *)
               apply negb_false_iff, Z.ltb_lt in Hc5.
               assert (Hres : Rate.parse_model (x_bs x) = (None, 0)).
               { apply (reac_rate_prop_parse.parse_model_no_params _ Hobj).
                 destruct (length (x_bs x)) as [|f] eqn:EL; [unfold x_len in Hl8; rewrite EL in Hl8; cbn in Hl8; lia|].
                 cbn [Spa.find_prop]. unfold Spa.prop_is_inside, Spa.ptr_type_inside, Spa.ptrinside.
                 replace (16 <=? Spa.u32_at (x_bs x) 0) with false by (symmetry; apply Z.leb_gt; lia).
                 reflexivity. }
               pe_run; [pe_awr|]. pe_keep. e2_leafT Hpre H2 Hcs HE Hres.
Qed.

End b.
