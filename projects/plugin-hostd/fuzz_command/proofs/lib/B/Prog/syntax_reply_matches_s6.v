(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (a loop by fuel induction,
   tcbb_loopX) and lib/A/AChd.v at c8557374ad2e: the walk of syntax_reply_matches on fuzz_command.asan, the scan of one
   item of the shape (the plain scan_loop, lib/Prog/syntax_reply_matches.v): L2 (0x88634, the end test at depth 0),
   L2D (0x8863c, the depth update) and L2T (0x88664, check C2 and the next byte). *)
(* Modified by Theorem Labs, 2026-10: re-walked from lib/A/Prog/syntax_reply_matches_s6.v (a working branch
   db7d4effe38) for fuzz_command.asan-ubsan: L2 0x8895c (the ' ' test first, then the depth), L2D 0x88964 with the
   UBSan check of `depth++` (0x88980: depth + 1 < depth, excluded since depth < 2^31 - 1), L2T 0x88994 with the
   UBSan check of `p++` (0x88994: s2 = -1, decided by s2 <= CEIL_HI); '[' = 91 is in a6, ']' = 93 in s1, 'Z' = 90
   in s10, '<' = 60 in s9. *)
(* Modified by Theorem Labs, 2026-10: onto a working branch 713692f1e0c (statement pass 4b): ABCMP and ASTRCSPN hold at
   every FP state, as the statement has them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa
  CmdPaLib PaSB PaDenot CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import syntax_reply_matches_c syntax_reply_matches_s1
  syntax_reply_matches_s2 syntax_reply_matches_s3 syntax_reply_matches_s4 syntax_reply_matches_s5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition SRM_L2D : Z := 0x2434.
Definition SRM_L2T : Z := 0x2464.

(* a signed compare of two values below 2^63 is the unsigned one *)
Lemma branch_lt_U63 : forall E a b, 0 <= U E a < 2 ^ 63 -> 0 <= U E b < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof.
intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned.
fold (U E a). fold (U E b). rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Lemma branch_ge_U63 : forall E a b, 0 <= U E a < 2 ^ 63 -> 0 <= U E b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof.
intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned.
fold (U E a). fold (U E b). rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
(* a signed branch over two of the walk's small values, as the unsigned one *)
Ltac lt_side := repeat (rewrite U_SOff || rewrite U_SLit); cbn [ew ewset Nat.eqb];
  repeat match goal with V : bv_unsigned (ew ?E ?n) = _ |- _ => rewrite V end;
  unfold zcanon, M64; rewrite ?Z.add_0_r, ?Z.mod_small by lia; lia.
Ltac lt_norm H := first [ rewrite branch_lt_U63 in H by lt_side | rewrite branch_ge_U63 in H by lt_side ].
(* a 32-bit ALU result (addiw, subw), as its unsigned value *)
Lemma U_aluw : forall E op a b,
  U E (SAluw op a b) = bv_swrap 32 (zalu_raw 31 32 op (U E a mod 2 ^ 32) (U E b mod 2 ^ 32)) mod 2 ^ 64.
Proof. intros E op a b. unfold U. rewrite unsigned_is_wrap_signed. fold (Sg E (SAluw op a b)). rewrite S_SAluw. reflexivity. Qed.
(* drop the reductions of small values, inner ones first when an outer one is not yet small *)
Ltac zsmall := repeat match goal with
  | |- context [?a mod ?m] => rewrite (Z.mod_small a m) by lia
  | |- context [bv_swrap 32 ?a] => rewrite (swrap32_id a) by lia
  | |- context [bv_swrap 64 ?a] => rewrite (swrap64_id a) by (unfold half64; lia)
  end.
(* the UBSan check of `depth++` (addiw a2, a4, 1; blt a2, a4): no overflow below 2^31 - 1 *)
Lemma trap_addiw1 : forall E a d, U E a = d -> 0 <= d < 2 ^ 31 - 1 ->
  branch_taken BC_LT (sv_denot E (SAluw ALU_ADD a (SLit 1))) (sv_denot E a) = false.
Proof.
intros E a d Ha Hd.
assert (HU : U E (SAluw ALU_ADD a (SLit 1)) = d + 1).
{ rewrite U_aluw. cbn [zalu_raw]. rewrite U_SLit, Ha. unfold zcanon, M64. zsmall. reflexivity. }
rewrite branch_lt_U63 by (rewrite ?HU, ?Ha; lia). rewrite HU, Ha. apply Z.ltb_ge. lia.
Qed.

(* the shape's byte at i, as the model reads it *)
Lemma srm_byte_hd : forall (l : list byte) i, (i < length l)%nat -> srm_byte (l ++ [Z_to_bv 8 0]) i = bz (hd NUL (skipn i l)).
Proof. intros l i Hi. rewrite srm_byte_app_lt by exact Hi. unfold srm_byte, bz. rewrite hd_skipn_nth. reflexivity. Qed.
Lemma ilen_step : forall (l : list byte) i d, (i < length l)%nat ->
  PSRM.ilen d (skipn i l) =
  if (d =? 0) && (bz (hd NUL (skipn i l)) =? 32) then 0%nat else S (PSRM.ilen (PSRM.dstep d (hd NUL (skipn i l))) (skipn (S i) l)).
Proof. intros l i d Hi. rewrite (PSRM.hd_skipn_S l i Hi) at 1. rewrite PSRM.ilen_cons. reflexivity. Qed.
Lemma dstep_range : forall d b, 0 <= d -> 0 <= PSRM.dstep d b <= d + 1.
Proof.
intros d b Hd. unfold PSRM.dstep.
destruct ((bz b =? 60) || (bz b =? 91)); [lia|].
destruct (((bz b =? 62) || (bz b =? 93)) && (0 <? d)) eqn:E; [|lia].
apply andb_true_iff in E as [_ E]. apply Z.ltb_lt in E. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation STK := SYNTAX_REPLY_MATCHES_STK.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation INV := (srm_inv B).
#[local] Notation OK := (srm_ok B).
#[local] Notation AT := (srm_at B).

(* The scan loop's head L2 (0x8895c): s2 = P + k' + q, a2 = the shape's byte there, a4 = the depth d, a0 = s2 + 1,
   s3 = s4 = P + k' (the item's start). L = ilen 0 (skipn k' shape) is the item's length (lib/Prog/
   syntax_reply_matches.v:76), so that L = q + ilen d (skipn (k' + q) shape) on the way; the facts the strcspn call
   needs (CALL1, syntax_reply_matches_s5.v) are carried as they are. *)
Definition L2_stmt (x : srm_ctx) (n t : nat) : Prop :=
  forall regs m md k' q d j f'', INV x regs m md ->
  (length (x_shape x) - (k' + q) < t)%nat -> (k' + q < length (x_shape x))%nat -> 0 <= d <= Z.of_nat q ->
  PSRM.ilen 0 (skipn k' (x_shape x)) = (q + PSRM.ilen d (skipn (k' + q) (x_shape x)))%nat ->
  (1 <= PSRM.ilen 0 (skipn k' (x_shape x)))%nat -> (j <= length (x_reply x))%nat ->
  (length (x_shape x) - (k' + PSRM.ilen 0 (skipn k' (x_shape x))) < n)%nat ->
  (length (x_shape x) - (k' + PSRM.ilen 0 (skipn k' (x_shape x))) <= f'')%nat ->
  reply_matches_items (firstn (PSRM.ilen 0 (skipn k' (x_shape x))) (skipn k' (x_shape x)) ::
                       items_f f'' (skipn (k' + PSRM.ilen 0 (skipn k' (x_shape x))) (x_shape x))) (skipn j (x_reply x))
    = reply_matches (x_shape x) (x_reply x) ->
  getr regs 18 = w64 (x_P x + Z.of_nat (k' + q)) -> getr regs 19 = w64 (x_P x + Z.of_nat k') ->
  getr regs 20 = w64 (x_P x + Z.of_nat k') -> getr regs 10 = w64 (x_P x + Z.of_nat (k' + q) + 1) ->
  getr regs 12 = w64 (srm_byte (x_shape x ++ [Z_to_bv 8 0]) (k' + q)) -> getr regs 14 = w64 d ->
  getr regs 8 = w64 (x_R x + Z.of_nat j) -> getr regs 11 = w64 0x21160 -> getr regs 15 = w64 62 ->
  getr regs 16 = w64 91 ->
  AT x SRM_L2 regs m md.

(* ---- L2T (0x88994): the UBSan check of `p++` (s2 = -1 is excluded by s2 <= CEIL_HI), check C2 on the next byte,
   step s2 and a0, load it; back to L2, or the item ends ---- *)
Definition l2t_region : YP09.region := YP09.mkRegion (Some 18%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))].
Definition l2t_facts : list (nat * afact) :=
  [(10%nat, mkAF 0 CEIL_HI 0); (18%nat, mkAF 0 CEIL_HI 0); (23%nat, mkAF (2 ^ 64 - 1) (2 ^ 64 - 1) 0);
   (24%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0)].
Lemma srm_L2T : forall x n t regs m md k' q d' j f'', OK x -> INV x regs m md -> L0_stmt B x n -> L2_stmt x n t ->
  (length (x_shape x) - (k' + q + 1) < t)%nat -> (k' + q < length (x_shape x))%nat -> 0 <= d' <= Z.of_nat q + 1 ->
  PSRM.ilen 0 (skipn k' (x_shape x)) = (q + 1 + PSRM.ilen d' (skipn (k' + q + 1) (x_shape x)))%nat ->
  (1 <= PSRM.ilen 0 (skipn k' (x_shape x)))%nat -> (j <= length (x_reply x))%nat ->
  (length (x_shape x) - (k' + PSRM.ilen 0 (skipn k' (x_shape x))) < n)%nat ->
  (length (x_shape x) - (k' + PSRM.ilen 0 (skipn k' (x_shape x))) <= f'')%nat ->
  reply_matches_items (firstn (PSRM.ilen 0 (skipn k' (x_shape x))) (skipn k' (x_shape x)) ::
                       items_f f'' (skipn (k' + PSRM.ilen 0 (skipn k' (x_shape x))) (x_shape x))) (skipn j (x_reply x))
    = reply_matches (x_shape x) (x_reply x) ->
  getr regs 18 = w64 (x_P x + Z.of_nat (k' + q)) -> getr regs 19 = w64 (x_P x + Z.of_nat k') ->
  getr regs 20 = w64 (x_P x + Z.of_nat k') -> getr regs 10 = w64 (x_P x + Z.of_nat (k' + q) + 1) ->
  getr regs 14 = w64 d' ->
  getr regs 8 = w64 (x_R x + Z.of_nat j) -> getr regs 11 = w64 0x21160 -> getr regs 15 = w64 62 ->
  getr regs 16 = w64 91 ->
  AT x SRM_L2T regs m md.
Proof.
intros x n t regs m md k' q d' j f'' HX HI IHL0 IH2 Ht Hq Hd HL HL1 Hj Hn Hf HV1 H18 H19 H20 H10 H14 H8 H11 H15 H16.
unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R24 & R22 & R25 & R26 & R9 & R23).
pose proof HX as (_ & _ & _ & [_ HSn] & _ & _ & _ & HSA & _).
set (b := srm_byte (x_shape x ++ [Z_to_bv 8 0]) (k' + q + 1)).
pose proof (srm_byte_range (x_shape x ++ [Z_to_bv 8 0]) (k' + q + 1)) as Hb. fold b in Hb.
remember (Eimg (Ereg regs [w64 b])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 b]) E) by (subst E; split; [intros r Hr; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (V10 : bv_unsigned (ew E 10) = x_P x + Z.of_nat (k' + q) + 1) by (subst E; apply (ew_EI_w64 regs _ 10 10%bv); [lia | reflexivity | exact H10 | lia]).
assert (V18 : bv_unsigned (ew E 18) = x_P x + Z.of_nat (k' + q)) by (subst E; apply (ew_EI_w64 regs _ 18 18%bv); [lia | reflexivity | exact H18 | lia]).
assert (V23 : bv_unsigned (ew E 23) = 2 ^ 64 - 1) by (subst E; apply (ew_EI_w64 regs _ 23 23%bv); [lia | reflexivity | exact R23 | lia]).
assert (V24 : bv_unsigned (ew E 24) = SB) by (subst E; apply (ew_EI_w64 regs _ 24 24%bv); [lia | reflexivity | exact R24 | unfold SB; lia]).
assert (V32 : bv_unsigned (ew E 32) = b) by (subst E; apply (ew_EX_w64 regs _ 0); [lia | reflexivity | lia]).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_L2T (srm_pins sr_atoms []) [l2t_region] None (mkFacts l2t_facts [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_L2T)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed.
  - constructor.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, l2t_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite V18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply (chunk_ok_val SEGS _ _ _ 1 1 (SOff 32 0) b).
    + apply sv_w64. rewrite U_SOff, V32. unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. lia.
    + simpl. lia.
    + lia.
    + change (N.to_nat 1) with 1%nat. apply val_mem1_of_aview.
      replace (x_P x + Z.of_nat (k' + q) + 1) with (x_P x + Z.of_nat (k' + q + 1)) by lia.
      exact (srm_shape_byte B x regs m md (k' + q + 1) HX HI ltac:(lia)).
  - cbn. tauto.
  - unfold facts_ok, l2t_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite V10, V18, V23, V24, V32. unfold CEIL_HI, SB. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan.
all: first [ awr_ok_tac | idtac ].
{ (* C2: the shape's next byte *)
  change (rd_of SEGS (mrestrict (w_H (x_W x)) m)) with (rdW (x_W x) m). unfold SRM_Bx.
  rewrite !U_SOff, V24, V10. unfold zcanon, M64. rewrite !Z.add_0_r, !Z.mod_small by (unfold SB; lia).
  eapply (range_addressable_sub _ _ (x_P x) (Z.of_nat (length (x_shape x)) + 1));
    [ eapply (srm_ra_kept B x regs m md); [exact HX | exact HI | lia | lia | exact HSA] | lia | lia ]. }
assert (KM1 := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
- (* the next byte is not NUL: back to L2 *)
  unorm Hc. bnorm Hc.
  assert (Lq : (k' + q + 1 < length (x_shape x))%nat).
  { destruct (Nat.lt_ge_cases (k' + q + 1) (length (x_shape x))) as [L|L]; [exact L|]. exfalso. apply Hc.
    unfold b. replace (k' + q + 1)%nat with (length (x_shape x)) by lia. apply srm_byte_app_end. }
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L2; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0));
  srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 11; 14; 15; 16; 19; 20]%bv : list (bv 5)) HK2;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (IH2 (ms_regs msn) (ms_mem msn) _ k' (S q) d' j f'' HIn ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite HL; replace (k' + S q)%nat with (k' + q + 1)%nat by lia; lia) HL1 Hj Hn Hf HV1);
  [ srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; lia
  | rewrite (HK2 19%bv) by (cbn; tauto); exact H19
  | rewrite (HK2 20%bv) by (cbn; tauto); exact H20
  | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; lia
  | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; unfold b; f_equal; lia
  | rewrite (HK2 14%bv) by (cbn; tauto); exact H14
  | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
  | rewrite (HK2 11%bv) by (cbn; tauto); exact H11
  | rewrite (HK2 15%bv) by (cbn; tauto); exact H15
  | rewrite (HK2 16%bv) by (cbn; tauto); exact H16 ]
  end.
- (* NUL: the shape ends, and with it the item; the strcspn call *)
  unorm Hc. bnorm Hc.
  assert (Lq : (k' + q + 1 = length (x_shape x))%nat).
  { destruct (Nat.lt_ge_cases (k' + q + 1) (length (x_shape x))) as [L|L]; [|lia]. exfalso.
    refine (srm_byte_le (x_shape x) (k' + q + 1) L HSn _). unfold b in Hc. rewrite srm_byte_app_lt in Hc by exact L. exact Hc. }
  assert (HLq : PSRM.ilen 0 (skipn k' (x_shape x)) = (q + 1)%nat).
  { rewrite HL, Lq, skipn_all, PSRM.ilen_nil. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_CALL1; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0));
  srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 11; 19; 20]%bv : list (bv 5)) HK2;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (srm_call1 B LAWS TL ABCMP ASTRCSPN x n (ms_regs msn) (ms_mem msn) _ k' (PSRM.ilen 0 (skipn k' (x_shape x))) f'' j
    HX HIn IHL0 Hj HL1 ltac:(lia) Hn Hf HV1);
  [ rewrite (HK2 8%bv) by (cbn; tauto); exact H8
  | rewrite (HK2 11%bv) by (cbn; tauto); exact H11
  | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; rewrite HLq; lia
  | rewrite (HK2 19%bv) by (cbn; tauto); exact H19
  | rewrite (HK2 20%bv) by (cbn; tauto); exact H20 ]
  end.
Qed.

(* ---- L2D (0x88964): the depth update, '<' or '[' opens (with the UBSan check 0x88980 of `depth++`), '>' or ']'
   closes when the depth is positive ---- *)
Lemma srm_L2D : forall x n t regs m md k' q d j f'', OK x -> INV x regs m md -> L0_stmt B x n -> L2_stmt x n t ->
  (length (x_shape x) - (k' + q + 1) < t)%nat -> (k' + q < length (x_shape x))%nat -> 0 <= d <= Z.of_nat q ->
  (d =? 0) && (srm_byte (x_shape x ++ [Z_to_bv 8 0]) (k' + q) =? 32) = false ->
  PSRM.ilen 0 (skipn k' (x_shape x)) = (q + PSRM.ilen d (skipn (k' + q) (x_shape x)))%nat ->
  (1 <= PSRM.ilen 0 (skipn k' (x_shape x)))%nat -> (j <= length (x_reply x))%nat ->
  (length (x_shape x) - (k' + PSRM.ilen 0 (skipn k' (x_shape x))) < n)%nat ->
  (length (x_shape x) - (k' + PSRM.ilen 0 (skipn k' (x_shape x))) <= f'')%nat ->
  reply_matches_items (firstn (PSRM.ilen 0 (skipn k' (x_shape x))) (skipn k' (x_shape x)) ::
                       items_f f'' (skipn (k' + PSRM.ilen 0 (skipn k' (x_shape x))) (x_shape x))) (skipn j (x_reply x))
    = reply_matches (x_shape x) (x_reply x) ->
  getr regs 18 = w64 (x_P x + Z.of_nat (k' + q)) -> getr regs 19 = w64 (x_P x + Z.of_nat k') ->
  getr regs 20 = w64 (x_P x + Z.of_nat k') -> getr regs 10 = w64 (x_P x + Z.of_nat (k' + q) + 1) ->
  getr regs 12 = w64 (srm_byte (x_shape x ++ [Z_to_bv 8 0]) (k' + q)) -> getr regs 14 = w64 d ->
  getr regs 8 = w64 (x_R x + Z.of_nat j) -> getr regs 11 = w64 0x21160 -> getr regs 15 = w64 62 ->
  getr regs 16 = w64 91 ->
  AT x SRM_L2D regs m md.
Proof.
intros x n t regs m md k' q d j f'' HX HI IHL0 IH2 Ht Hq Hd Hns HL HL1 Hj Hn Hf HV1 H18 H19 H20 H10 H12 H14 H8 H11 H15 H16.
unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R24 & R22 & R25 & R26 & R9 & R23).
set (b := srm_byte (x_shape x ++ [Z_to_bv 8 0]) (k' + q)) in *.
pose proof (srm_byte_range (x_shape x ++ [Z_to_bv 8 0]) (k' + q)) as Hb. fold b in Hb.
assert (Hcb : bz (hd NUL (skipn (k' + q) (x_shape x))) = b) by (unfold b; symmetry; apply srm_byte_hd; exact Hq).
(* the item goes on past this byte *)
assert (HL' : PSRM.ilen 0 (skipn k' (x_shape x)) =
  (q + 1 + PSRM.ilen (PSRM.dstep d (hd NUL (skipn (k' + q) (x_shape x)))) (skipn (k' + q + 1) (x_shape x)))%nat).
{ rewrite HL, (ilen_step _ _ d Hq), Hcb, Hns. replace (S (k' + q)) with (k' + q + 1)%nat by lia. lia. }
pose proof (dstep_range d (hd NUL (skipn (k' + q) (x_shape x))) ltac:(lia)) as Hdr.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros r Hr; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (V12 : bv_unsigned (ew E 12) = b) by (subst E; apply (ew_EI_w64 regs _ 12 12%bv); [lia | reflexivity | exact H12 | lia]).
assert (V14 : bv_unsigned (ew E 14) = d) by (subst E; apply (ew_EI_w64 regs _ 14 14%bv); [lia | reflexivity | exact H14 | lia]).
assert (V15 : bv_unsigned (ew E 15) = 62) by (subst E; apply (ew_EI_w64 regs _ 15 15%bv); [lia | reflexivity | exact H15 | lia]).
assert (V16 : bv_unsigned (ew E 16) = 91) by (subst E; apply (ew_EI_w64 regs _ 16 16%bv); [lia | reflexivity | exact H16 | lia]).
assert (V25 : bv_unsigned (ew E 25) = 60) by (subst E; apply (ew_EI_w64 regs _ 25 25%bv); [lia | reflexivity | exact R25 | lia]).
assert (V26 : bv_unsigned (ew E 26) = 90) by (subst E; apply (ew_EI_w64 regs _ 26 26%bv); [lia | reflexivity | exact R26 | lia]).
assert (V9 : bv_unsigned (ew E 9) = 93) by (subst E; apply (ew_EI_w64 regs _ 9 9%bv); [lia | reflexivity | exact R9 | lia]).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_L2D (srm_pins sr_atoms []) [] None (mkFacts [] [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_L2D)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed; first [apply Forall_nil | vm_compute; reflexivity | exact I | (split; [exact I | split; exact I])]. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
assert (KM1 := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
(* the leaf: on to L2T with the new depth *)
let leaf := idtac;
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L2T; [awr_ok_tac|];
  lazymatch type of HS with context [restrict _ ?msn] =>
  let KM := fresh "KM" in let HK := fresh "HK" in let HK2 := fresh "HK2" in let HIn := fresh "HIn" in
  assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0);
        first [exact (KM4 a0 Ha0) | exact (KM3 a0 Ha0) | exact (KM2 a0 Ha0) | exact (KM1 a0 Ha0)]);
  srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 10; 11; 15; 16; 18; 19; 20]%bv : list (bv 5)) HK2;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (srm_L2T x n t (ms_regs msn) (ms_mem msn) _ k' q (PSRM.dstep d (hd NUL (skipn (k' + q) (x_shape x)))) j f''
    HX HIn IHL0 IH2 Ht Hq ltac:(lia) HL' HL1 Hj Hn Hf HV1);
  [ rewrite (HK2 18%bv) by (cbn; tauto); exact H18
  | rewrite (HK2 19%bv) by (cbn; tauto); exact H19
  | rewrite (HK2 20%bv) by (cbn; tauto); exact H20
  | rewrite (HK2 10%bv) by (cbn; tauto); exact H10
  | (* after an opening bracket a4 = a2 + 0, a2 = depth + 1 (addiw): two passes over the 64- and 32-bit values *)
    srm_rgoal HS; rewrite ?U_aluw; cbn [zalu_raw]; srm_ucalc; rewrite ?U_aluw; cbn [zalu_raw]; srm_ucalc; zsmall;
    repeat match goal with |- context [if ?c then _ else _] => let Ec := fresh "Ec" in destruct c eqn:Ec end; zsmall;
    unfold PSRM.dstep; rewrite Hcb;
    destruct (Z.eqb_spec b 60), (Z.eqb_spec b 91), (Z.eqb_spec b 62), (Z.eqb_spec b 93), (Z.ltb_spec 0 d);
    cbn [orb andb];
    repeat match goal with H : (_ <? _) = true |- _ => apply Z.ltb_lt in H | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H end;
    zsmall; lia
  | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
  | rewrite (HK2 11%bv) by (cbn; tauto); exact H11
  | rewrite (HK2 15%bv) by (cbn; tauto); exact H15
  | rewrite (HK2 16%bv) by (cbn; tauto); exact H16 ]
  end in
let step K := idtac;
  paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|];
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (K : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0);
        first [exact (KM3 a0 Ha0) | exact (KM2 a0 Ha0) | exact (KM1 a0 Ha0)])
  end; clear HF HFr HG in
(* an opening bracket: `depth++` (addiw a2, a4, 1) and its UBSan check (blt a2, a4 to the trap), then the leaf *)
let opens K := idtac;
  step K; psrr_branch_tok RUN BR HS SHOK SRM_Bspan;
  [ exfalso; lazymatch goal with Htr : branch_taken BC_LT _ _ = true |- _ =>
      rewrite (trap_addiw1 E (SOff 14 0) d) in Htr;
      [ discriminate Htr
      | rewrite U_SOff, V14; unfold zcanon, M64; rewrite Z.add_0_r; apply Z.mod_small; lia
      | lia ] end
  | leaf ] in
psrr_branch_tok RUN BR HS SHOK SRM_Bspan;
[ (* 90 < b *)
  lt_norm Hc; unorm Hc; bnorm Hc; step KM2; psrr_branch_tok RUN BR HS SHOK SRM_Bspan;
  [ (* ']' closes *) unorm Hc0; bnorm Hc0; leaf
  | unorm Hc0; bnorm Hc0; step KM3; psrr_branch_tok RUN BR HS SHOK SRM_Bspan;
    [ (* no change *) unorm Hc1; bnorm Hc1; leaf | (* '[' opens *) unorm Hc1; bnorm Hc1; opens KM4 ] ]
| (* b <= 90 *)
  lt_norm Hc; unorm Hc; bnorm Hc; step KM2; psrr_branch_tok RUN BR HS SHOK SRM_Bspan;
  [ (* '<' opens *) unorm Hc0; bnorm Hc0; opens KM3
  | unorm Hc0; bnorm Hc0; step KM3; psrr_branch_tok RUN BR HS SHOK SRM_Bspan;
    [ (* '>' closes *) unorm Hc1; bnorm Hc1; leaf | (* no change *) unorm Hc1; bnorm Hc1; leaf ] ] ].
Qed.

(* ---- L2 (0x8895c): a byte other than ' ' goes to the depth update; a ' ' at depth 0 ends the item (the strcspn
   call), at a positive depth it goes to the depth update. By fuel induction over the bytes left (cgif A/AC8b.v's
   tcbb_loopX). ---- *)
Lemma srm_L2 : forall x n t, OK x -> L0_stmt B x n -> L2_stmt x n t.
Proof.
intros x n t HX IHL0. induction t as [|t IH2];
  intros regs m md k' q d j f'' HI Ht Hq Hd HL HL1 Hj Hn Hf HV1 H18 H19 H20 H10 H12 H14 H8 H11 H15 H16; [lia|].
unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R24 & R22 & R25 & R26 & R9 & R23).
set (b := srm_byte (x_shape x ++ [Z_to_bv 8 0]) (k' + q)) in *.
pose proof (srm_byte_range (x_shape x ++ [Z_to_bv 8 0]) (k' + q)) as Hb. fold b in Hb.
assert (Hcb : bz (hd NUL (skipn (k' + q) (x_shape x))) = b) by (unfold b; symmetry; apply srm_byte_hd; exact Hq).
assert (Ht' : (length (x_shape x) - (k' + q + 1) < t)%nat) by lia.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros r Hr; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (V12 : bv_unsigned (ew E 12) = b) by (subst E; apply (ew_EI_w64 regs _ 12 12%bv); [lia | reflexivity | exact H12 | lia]).
assert (V14 : bv_unsigned (ew E 14) = d) by (subst E; apply (ew_EI_w64 regs _ 14 14%bv); [lia | reflexivity | exact H14 | lia]).
assert (V22 : bv_unsigned (ew E 22) = 32) by (subst E; apply (ew_EI_w64 regs _ 22 22%bv); [lia | reflexivity | exact R22 | lia]).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_L2 (srm_pins sr_atoms []) [] None (mkFacts [] [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_L2)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed; first [apply Forall_nil | vm_compute; reflexivity | exact I | (split; [exact I | split; exact I])]. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
assert (KM1 := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
let toL2D KMx Hns := idtac;
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L2D; [awr_ok_tac|];
  lazymatch type of HS with context [restrict _ ?msn] =>
  let KM := fresh "KM" in let HK := fresh "HK" in let HK2 := fresh "HK2" in let HIn := fresh "HIn" in
  assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KMx a0 Ha0));
  srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 10; 11; 12; 14; 15; 16; 18; 19; 20]%bv : list (bv 5)) HK2;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (srm_L2D x n t (ms_regs msn) (ms_mem msn) _ k' q d j f'' HX HIn IHL0 IH2 Ht' Hq Hd Hns HL HL1 Hj Hn Hf HV1);
  [ rewrite (HK2 18%bv) by (cbn; tauto); exact H18
  | rewrite (HK2 19%bv) by (cbn; tauto); exact H19
  | rewrite (HK2 20%bv) by (cbn; tauto); exact H20
  | rewrite (HK2 10%bv) by (cbn; tauto); exact H10
  | rewrite (HK2 12%bv) by (cbn; tauto); exact H12
  | rewrite (HK2 14%bv) by (cbn; tauto); exact H14
  | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
  | rewrite (HK2 11%bv) by (cbn; tauto); exact H11
  | rewrite (HK2 15%bv) by (cbn; tauto); exact H15
  | rewrite (HK2 16%bv) by (cbn; tauto); exact H16 ]
  end in
psrr_branch_tok RUN BR HS SHOK SRM_Bspan;
[ (* b <> ' ': the depth update *)
  unorm Hc; bnorm Hc;
  assert (Hns : (d =? 0) && (b =? 32) = false) by (rewrite (proj2 (Z.eqb_neq b 32)) by lia; apply andb_false_r);
  toL2D KM1 Hns
| (* b = ' ' *)
  unorm Hc; bnorm Hc;
  paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|];
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM2 : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0))
  end; clear HF HFr HG;
  psrr_branch_tok RUN BR HS SHOK SRM_Bspan;
  [ (* depth <= 0, so 0: the item ends here; the strcspn call *)
    lt_norm Hc0; unorm Hc0; bnorm Hc0;
    assert (HLq : PSRM.ilen 0 (skipn k' (x_shape x)) = q)
      by (rewrite HL, (ilen_step _ _ d Hq), Hcb; replace d with 0 by lia; rewrite Hc; cbn; lia);
    paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_CALL1; [awr_ok_tac|];
    lazymatch type of HS with context [restrict _ ?msn] =>
    assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
      by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM2 a0 Ha0));
    srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 11; 18; 19; 20]%bv : list (bv 5)) HK2;
    pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
    pmkst HS;
    eapply (srm_call1 B LAWS TL ABCMP ASTRCSPN x n (ms_regs msn) (ms_mem msn) _ k' (PSRM.ilen 0 (skipn k' (x_shape x))) f''
      j HX HIn IHL0 Hj HL1 ltac:(lia) Hn Hf HV1);
    [ rewrite (HK2 8%bv) by (cbn; tauto); exact H8
    | rewrite (HK2 11%bv) by (cbn; tauto); exact H11
    | rewrite (HK2 18%bv) by (cbn; tauto); rewrite HLq; exact H18
    | rewrite (HK2 19%bv) by (cbn; tauto); exact H19
    | rewrite (HK2 20%bv) by (cbn; tauto); exact H20 ]
    end
  | (* 0 < depth: inside brackets a ' ' does not end the item *)
    lt_norm Hc0; unorm Hc0; bnorm Hc0;
    assert (Hns : (d =? 0) && (b =? 32) = false) by (rewrite (proj2 (Z.eqb_neq d 0)) by lia; reflexivity);
    toL2D KM2 Hns ] ].
Qed.
End e.
End f.
End d.
