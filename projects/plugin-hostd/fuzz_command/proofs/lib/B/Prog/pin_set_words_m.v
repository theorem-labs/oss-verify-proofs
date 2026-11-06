(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of answer_code on plugin-hostd/fuzz_command's ASan build, in the shape of proofs/cgif/cgif_file_fuzzer/lib/A/ACbl.v (entry state, run, call, return), A/AChf.v (a side-stack frame taken by __asan_stack_malloc_N, its header and shadow) and A/AChx.v (its release by the flag store); the frame-flag law is A/ACed.v's tfibX_FFL. The snprintf call goes through the shared contract (lib/A/Rt/RtPFShared.v) and the FP lifts of lib/A/Prog/PaFx.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_code.v, with its module paths and module names changed; 357 of its 414 lines of code are new or changed and 1174 lines of the source are left out. *)
(* Segment M of the walk of pin_set_words on the ASan+UBSan build of plugin-hostd/fuzz_command (image B,
   fuzz_command.asan-ubsan; the interface lib/B/Prog/pin_set_words_s4.v): from MID (0x8e228) to JOIN (0x8e284).

     0x8e228  li a0,5 ; bne s3,a0          ntok = 4: 0x8e280 li a3,0 ; JOIN with no verdict (a3 = 0)
     0x8e230  .. 0x8e240                   ntok = 5: the UBSan checks of tok + 32 (wrap 0x8e234, misaligned 0x8e240)
     0x8e244  .. 0x8e250                   the inline load8 check of tok + 32 (shadow entry [tok, tok + 40))
     0x8e254  ld s3,0(a0)                  tok[4]
     0x8e258  .. 0x8e268                   strncmp(tok[4], "verdict=" (0x22900), 8) through PaArtStr.v's aj_strncmp_at
     0x8e26c  bnez a0                      <> 0: the epilogue 0x8e2ec and the ret 0x8e30c with s2 = -902 (R4)
     0x8e270  addi a3,s3,8 ; li a0,9 ; bgeu a3,a0,JOIN    = 0: JOIN with the verdict tok[4] + 8; the UBSan `j` at
                                           0x8e27c (tok[4] + 8 < 9 unsigned) is not reached
   The two checks on tok are decided by the symbolic run from the seed's fact on tok (atom 8). The check at 0x8e27c
   is decided by the run from a fact on tok[4] (atom 40: in [4096, 0x7fffff800000)) that this file adds to the seed:
   tok[4] lies in the block (cb, ncb) of atoks_atA, with 4096 <= cb and cb + ncb <= alloc_ceiling (AR's al_blocks).

   The symbolic state is s4's psw_seedJ at PSW_MID (atom 40 = tok[4] when ntok = 5, as one more read-only region by
   psw_add_tok); no instruction of this segment writes memory, so each run keeps every byte (psw_frame_same), and
   strncmp writes only its scratch window below sp0 - 48. The B twin of a Theorem Labs lane's A file lib/A/Prog/pin_set_words_m.v
   (B pcs, B's s1 = tok[3] and s2 = the result, the UBSan checks, the fx-generic STRNCMP, PaArtStr.v's errno fact
   CmdRecCells.cmd_cf_env in place of PALib's pal_env). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecCells.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pin_set_words_s1 pin_set_words_s2 pin_set_words_s3.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pins_set_c lv2_refusals_forget_c pin_set_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pin_set_words_s4 PaArtStr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma pm_list5 : forall {A} (l : list A), length l = 5%nat -> exists a b c d e, l = [a; b; c; d; e].
Proof.
intros A l H. destruct l as [|a [|b [|c [|d [|e [|x l]]]]]]; cbn [length] in H; try lia.
exists a, b, c, d, e. reflexivity.
Qed.
Lemma pm_saved_kept : forall regs (rd rd' : reader) lo hi, psw_saved regs rd -> kept_out rd rd' lo hi ->
hi <= spZ regs - 48 -> 48 <= spZ regs -> spZ regs <= 2 ^ 64 -> psw_saved regs rd'.
Proof.
intros regs rd rd' lo hi (S1 & S8 & S9 & S18 & S19 & S20) HK Hhi H48 H64.
assert (A : forall a v, spZ regs - 48 <= a -> a + 8 <= spZ regs -> aval_mem rd a 8 v -> aval_mem rd' a 8 v).
{ intros a v Ha1 Ha2 Hv. apply (aval_mem_agree rd rd' a 8 v Hv). intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply HK; lia. }
unfold psw_saved. repeat split; apply A; first [lia | assumption].
Qed.
Lemma pm_ew_agree : forall k E0 E n, env_agree k E0 E -> (n < k)%nat -> ew E n = ew E0 n.
Proof. intros k E0 E n [HA _] Hn. exact (HA n Hn). Qed.
Lemma pm_ne_lit : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = negb (v =? z).
Proof.
intros E n v z Hn Hv Hz. rewrite branch_ne_U, (U_atom E n v Hn Hv), U_SLit. rewrite (zcanon_id z) by (unfold M64; lia).
reflexivity.
Qed.
Lemma pm_ne0 : forall E n (w : word), ew E n = w ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (bv_unsigned w =? 0).
Proof.
intros E n w Hn. rewrite branch_ne_U, U_SOff, U_SLit, Hn, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite (zcanon_id (bv_unsigned w)) by (unfold M64; lia). reflexivity.
Qed.
Lemma pm_w0 : forall w : word, bv_unsigned w = 0 -> w = w64 0.
Proof. intros w H. apply bv_eq. rewrite H. reflexivity. Qed.
Lemma pm_havoc_a0 : forall E k (regs2 : bvmap 5 word), ew (havoc E k (map (getr regs2) CLOB)) (k + 4) = getr regs2 10.
Proof. intros E k regs2. rewrite (ew_havoc_new E k _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia). reflexivity. Qed.
(* the registers JOIN reads or hands back that this segment does not write: sp, gp, tp, s0, s1 (tok[3]), s4,
   s5..s11 *)
Definition pm_keep_regs : list (bv 5) :=
[2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 20%bv] ++ map (Z_to_bv 5) [21; 22; 23; 24; 25; 26; 27].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* after check_words_pin_set.v's cw_region_kept / hull_sub / aread_ok_prefix / cw_img_atom *)
Lemma pm_region_kept : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma pm_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H.
pose proof (shadow_mono x x' H1) as M1. pose proof (shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma pm_aread_ok_prefix : forall stk W regs mem x n n', aread_ok SEGS stk W regs mem x n -> 0 <= n' <= n ->
aread_ok SEGS stk W regs mem x n'.
Proof.
intros stk W regs mem x n n' (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hn.
split; [lia|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply H3; lia|].
split; [unfold amem_range in *; lia|]. split; [eapply range_addressable_sub; [exact H5 | lia | lia]|].
intros Hp. apply (pm_hull_sub _ x n x n'); [apply H6; lia | lia | lia | lia].
Qed.
Lemma pm_img_atom : forall E a, img_env VAL A_LIM E -> (A_TEXT <= a < A_LIM)%nat -> ew E a = Z_to_bv 64 (VAL a).
Proof. intros E a HE Ha. rewrite <- (HE a Ha). symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* a run over read-only regions keeps every byte *)
Lemma pm_kept_run : forall (rd0 : reader) E rs H (m m' : word -> option byte) lo hi,
kept_out rd0 (aview SEGS H m) lo hi -> frame_of E rs (mrestrict H m) (mrestrict H m') -> psw_ro_regions rs = true ->
kept_out rd0 (aview SEGS H m') lo hi.
Proof.
intros rd0 E rs H m m' lo hi HK Hf Hro a Ha Hn. rewrite (psw_frame_same E rs H m m' Hf Hro a Ha). exact (HK a Ha Hn).
Qed.
(* the seed's environment *)
Lemma pm_ew_reg : forall (regs1 regs : bvmap 5 word) p1 p2 p4 n (r : bv 5), Z.of_nat n = bv_unsigned r ->
ew (EJ regs1 regs p1 p2 p4) n = getr regs1 r.
Proof. intros regs1 regs p1 p2 p4 n r Hn. unfold EJ. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma pm_ew40 : forall (regs1 regs : bvmap 5 word) p1 p2 p4, ew (EJ regs1 regs p1 p2 p4) 40 = Z_to_bv 64 p4.
Proof.
intros regs1 regs p1 p2 p4. unfold EJ. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs1 (psw_extraJ regs p1 p2 p4) 8).
Qed.
Lemma pm_agree32 : forall (regs1 regs : bvmap 5 word) p1 p2 p4 E, env_agree 41 (EJ regs1 regs p1 p2 p4) E ->
env_agree 32 (Ereg regs1 (psw_extraJ regs p1 p2 p4)) E.
Proof.
intros regs1 regs p1 p2 p4 E [HA HD]. split.
- intros n Hn. rewrite HA by lia. unfold EJ. apply Eimg_low. unfold A_TEXT. lia.
- rewrite HD. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the per-binary record (lib/B/YF0m.v) and the image facts (CmdRecBase.v): psw_blk_ready / psw_verdict_ready of s4,
   and the errno fact the strncmp call step asks (CmdRecCells.v's cmd_cf_env) *)
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
(* the meter laws (s4's psw_Q_reject) *)
Hypothesis MTL : ameter_laws MT.
(* the strncmp wrapper the statement names (pin_set_words_c.v:113), at every FP state *)
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

(* after each symbolic run: the bytes kept, the model term named (brief-cmdwalk.md TRAP) *)
Ltac pm_keep KM :=
lazymatch goal with HFr : frame_of ?E ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
let K2 := fresh "KM" in
pose proof (pm_kept_run _ E rs H m0 m1 _ _ KM HFr ltac:(vm_compute; reflexivity)) as K2;
clear KM; rename K2 into KM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
repeat match goal with H1 : img_env ?v ?l ?e, H2 : img_env ?v ?l ?e |- _ => clear H2 end.
Ltac pm_md := lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ =>
let mdv := fresh "mdv" in set (mdv := d) in *; clearbody mdv end.
Ltac pm_in := cbn [In app map]; repeat (first [left; reflexivity | right]).
(* at JOIN: the pc named, then the hypothesis from_JOIN *)
Ltac pm_join FJ :=
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?k)) _ _) _) _ =>
replace k with PSW_JOIN by (vm_compute; reflexivity) end;
apply FJ; unfold INV_JOIN.
(* the cut record at JOIN: the journal, the kept memory, the saved words and the registers *)
Ltac pm_cut HJ HK0 KM HSV HKR Q2 Q3 Q4 Q8 Q9 Q20 Qhi :=
constructor;
[ exact HJ
| exact (kept_out_trans _ _ _ _ _ _ _ HK0 KM ltac:(lia) ltac:(lia))
| exact (pm_saved_kept _ _ _ _ _ HSV KM ltac:(lia) ltac:(lia) ltac:(lia))
| rewrite (HKR 2%bv ltac:(unfold pm_keep_regs; pm_in)); exact Q2
| rewrite (HKR 3%bv ltac:(unfold pm_keep_regs; pm_in)); exact Q3
| rewrite (HKR 4%bv ltac:(unfold pm_keep_regs; pm_in)); exact Q4
| rewrite (HKR 8%bv ltac:(unfold pm_keep_regs; pm_in)); exact Q8
| rewrite (HKR 9%bv ltac:(unfold pm_keep_regs; pm_in)); exact Q9
| rewrite (HKR 20%bv ltac:(unfold pm_keep_regs; pm_in)); exact Q20
| let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
  rewrite (HKR (Z_to_bv 5 r)) by (unfold pm_keep_regs; apply in_or_app; right; apply in_map; cbn [In]; lia);
  exact (Qhi r Hr) ].

Theorem psw_M : forall c, psw_pre B MT c -> from_JOIN B MT c -> from_MID B MT c.
Proof.
intros c HP FJ. unfold from_MID, INV_MID.
intros regs1 memc mdc (p3 & w3 & HC & H18 & H19 & Hland & Hp3 & Hw3 & HlenT & Hdash).
destruct HC as [HJ HK0 HSV Q2 Q3 Q4 Q8 Q9 Q20 Qhi].
pose proof (pp_afn B MT c HP) as HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK48 : 48 + 2 * ESTACK <= PIN_SET_WORDS_STK).
{ unfold PIN_SET_WORDS_STK. pose proof (Z.le_max_l (2 * ESTACK) (Z.max PINS_SET_STK LV2_REFUSALS_FORGET_STK)). lia. }
assert (HES : ESTACK = 4096) by reflexivity.
pose proof (pp_tokobj B MT c HP) as ((cid & pos & Hfrm & Hcid & Hfal & Hflo & Hfhi) & Htok8 & HraT).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hfrm) as (Hf0 & Hfc & Hfapp).
pose proof (pp_toks B MT c HP) as HTOKS.
pose proof HTOKS as (_ & HlenP & HtokP & HtokW).
pose proof (pp_ntok B MT c HP) as Hntk. pose proof (pp_ntokr B MT c HP) as Hntokr.
assert (Hn45 : x_ntok c = 4 \/ x_ntok c = 5) by (apply psw_land_m2; [lia | exact Hland]).
unfold psw_sp0 in *. set (sp0 := spZ (x_regs c)) in *.
assert (Esp0 : sp0 = spZ (x_regs c)) by reflexivity.
assert (Htokb : 4096 <= x_tok c /\ x_tok c + 8 * x_ntok c <= alloc_ceiling) by lia.
pose proof (pp_vobjs B MT c HP) as HVO.
unfold from_JOIN in FJ.
destruct Hn45 as [Hn4 | Hn5].
- (* ntok = 4: li a3,0 and JOIN with no verdict *)
  assert (Lt : length (x_tks c) = 4%nat) by lia.
  destruct (psw_list4 _ Lt) as (t0 & u & f & l & Etks).
  assert (Lp : length (x_ptrs c) = 4%nat) by lia.
  destruct (psw_list4 _ Lp) as (q0 & q1 & q2 & q3 & Eptrs).
  rewrite Etks in Hw3. cbn in Hw3. injection Hw3 as Hw3. subst l.
  rewrite Eptrs in Hp3. cbn in Hp3. injection Hp3 as Hp3. subst q3.
  pose proof (psw_seedJ (x_ly c) (x_W c) memc (x_regs c) regs1 PSW_MID (x_tok c) 0 0 0 Hstk HSV Q2 Q8 Q20
    ltac:(lia) Htok8 ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
  assert (SHOK : sh_ok SEGS BxJ [] (EJ regs1 (x_regs c) 0 0 0) (mrestrict (w_H (x_W c)) memc)) by constructor.
  assert (HEI : img_env VAL A_LIM (EJ regs1 (x_regs c) 0 0 0)) by (unfold EJ; apply Eimg_env).
  assert (E19 : ew (EJ regs1 (x_regs c) 0 0 0) 19 = Z_to_bv 64 (x_ntok c))
    by (rewrite (pm_ew_reg _ _ _ _ _ 19 19%bv eq_refl); exact H19).
  remember (EJ regs1 (x_regs c) 0 0 0) as E0 eqn:HE0 in *.
  assert (HAG : env_agree 41 (EJ regs1 (x_regs c) 0 0 0) E0) by (rewrite HE0; apply env_agree_refl).
  clear HE0.
  assert (KM : kept_out (rdW (x_W c) memc) (rdW (x_W c) memc) (sp0 + -48 - 2 * ESTACK) (sp0 + -48))
    by (intros a _ _; reflexivity).
  (* li a0,5 ; bne s3,a0 *)
  paj_run_tok RUN HS HJ SHOK RBspanJ; [awr_ok_tac |].
  pm_keep KM. pm_md.
  psrr_branch_tok RUN BR HS SHOK RBspanJ.
  2:{ exfalso. rewrite (pm_ne_lit _ 19 (x_ntok c) 5 E19 ltac:(lia) ltac:(lia)), Hn4 in Hc.
      vm_compute in Hc. discriminate Hc. }
  (* 0x8e280 li a3,0, to JOIN *)
  paj_run_to_tok RUNTO HS HJ SHOK RBspanJ PSW_JOIN; [awr_ok_tac |].
  pm_keep KM. pm_md.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msJ end.
  prreg HS (13%bv : bv 5) R13.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ pm_keep_regs HS (pm_agree32 _ _ _ _ _ _ HAG)
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict mkst] in HKR.
  pmkst HS.
  pm_join FJ.
  exists q1, q2, p3, u, f, w3, None, 0.
  split; [pm_cut HJ HK0 KM HSV HKR Q2 Q3 Q4 Q8 Q9 Q20 Qhi|].
  split; [rewrite R13; reflexivity|].
  split; [rewrite Eptrs; reflexivity|].
  split; [rewrite Eptrs; reflexivity|].
  split; [rewrite Eptrs; reflexivity|].
  split; [rewrite Etks; reflexivity|].
  split; [rewrite Etks; reflexivity|].
  split; [rewrite Etks; reflexivity|].
  split; [rewrite Etks; cbn [tl]; exact (psw_m_len3 (x_T c) u f w3 HlenT Hdash)|].
  left. split; reflexivity.
- (* ntok = 5 *)
  assert (Lt : length (x_tks c) = 5%nat) by lia.
  destruct (pm_list5 _ Lt) as (t0 & u & f & l & w4 & Etks).
  assert (Lp : length (x_ptrs c) = 5%nat) by lia.
  destruct (pm_list5 _ Lp) as (q0 & q1 & q2 & q3 & q4 & Eptrs).
  rewrite Etks in Hw3. cbn in Hw3. injection Hw3 as Hw3. subst l.
  rewrite Eptrs in Hp3. cbn in Hp3. injection Hp3 as Hp3. subst q3.
  destruct (HtokW 4%nat q4 w4 ltac:(rewrite Eptrs; reflexivity) ltac:(rewrite Etks; reflexivity)) as (Hs4 & Hl4 & Hcb4 & Hce4).
  pose proof (HtokP 4%nat q4 ltac:(rewrite Eptrs; reflexivity)) as Hq4m.
  pose proof (pp_cb B MT c HP) as Hcb.
  destruct (al_blocks SEGS B LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hcb4096 & Hcbceil & _).
  pose proof (psw3_req_ge (x_ncb c)) as Hreqcb.
  assert (Rq4 : 4096 <= q4 /\ q4 + Z.of_nat (length w4) + 1 <= alloc_ceiling) by lia.
  pose proof (psw_seedJ (x_ly c) (x_W c) memc (x_regs c) regs1 PSW_MID (x_tok c) 0 0 q4 Hstk HSV Q2 Q8 Q20
    ltac:(lia) Htok8 ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
  assert (Hav4 : aval_mem (rdW (x_W c) memc) (x_tok c + 8 * 4) 8 q4).
  { apply (aval_mem_agree _ _ _ 8 q4 Hq4m). intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply HK0; lia. }
  assert (E8 : ew (EJ regs1 (x_regs c) 0 0 q4) 8 = Z_to_bv 64 (x_tok c))
    by (rewrite (pm_ew_reg _ _ _ _ _ 8 8%bv eq_refl); exact Q8).
  assert (E2 : ew (EJ regs1 (x_regs c) 0 0 q4) 2 = Z_to_bv 64 (sp0 - 48))
    by (rewrite (pm_ew_reg _ _ _ _ _ 2 2%bv eq_refl); exact Q2).
  assert (E20 : ew (EJ regs1 (x_regs c) 0 0 q4) 20 = Z_to_bv 64 SB)
    by (rewrite (pm_ew_reg _ _ _ _ _ 20 20%bv eq_refl); exact Q20).
  assert (Utok : bv_unsigned (ew (EJ regs1 (x_regs c) 0 0 q4) 8) = x_tok c) by (rewrite E8; apply unsigned_lit_small; lia).
  assert (Usp : bv_unsigned (ew (EJ regs1 (x_regs c) 0 0 q4) 2) = sp0 - 48) by (rewrite E2; apply unsigned_lit_small; lia).
  (* tok[4] as one more read-only region over s0 *)
  assert (HD : all_disjoint (EJ regs1 (x_regs c) 0 0 q4) (psw_tokJ 4 40) (ss_mem (ss_pswJ PSW_MID))).
  { apply all_disjoint_of_extents. unfold ss_pswJ, psw_frameJ, psw_tokJ, extent_of_region.
    cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]. rewrite Utok, Usp.
    split; [|exact I]. unfold zdisj. cbn [fst snd]. lia. }
  pose proof (psw_add_tok _ _ _ 4 40 (x_tok c) q4 HS ltac:(vm_compute; reflexivity) Utok (pm_ew40 _ _ _ _ _) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) (psw_val_mem_of_aval _ _ _ _ _ Hav4) HD) as HS4.
  clear HS HD. rename HS4 into HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_pswJ] in HS.
  (* tok[4]'s range, for the UBSan check at 0x8e27c (tok[4] + 8 < 9 unsigned) *)
  assert (F40 : afact_ok (EJ regs1 (x_regs c) 0 0 q4) 40%nat (mkAF 4096 (0x7fffff800000 - 1) 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite pm_ew40, unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  pose proof (st_ok_pi_add_fact _ _ _ 40%nat _ HS F40) as HS4.
  clear HS F40. rename HS4 into HS.
  (* the shadow entry of the load8 check of tok + 32 *)
  assert (SHOK : sh_ok SEGS BxJ [mkSHE 8 0 40] (EJ regs1 (x_regs c) 0 0 q4) (mrestrict (w_H (x_W c)) memc)).
  { apply (psw_shokJ (x_W c) memc _ (x_tok c) (x_ntok c) 40).
    - unfold BxJ. rewrite (U_atom _ 20 SB E20) by (unfold SB; lia). reflexivity.
    - apply (U_atom _ 8 (x_tok c) E8). lia.
    - apply (range_addressable_kept_win _ _ (sp0 - PIN_SET_WORDS_STK) sp0 (x_tok c) (8 * x_ntok c) HK0);
      [lia | lia | lia | exact HraT].
    - lia.
    - apply (in_app_sub _ _ _ _ Hfapp); lia.
    - lia. }
  assert (HEI : img_env VAL A_LIM (EJ regs1 (x_regs c) 0 0 q4)) by (unfold EJ; apply Eimg_env).
  assert (E19 : ew (EJ regs1 (x_regs c) 0 0 q4) 19 = Z_to_bv 64 (x_ntok c))
    by (rewrite (pm_ew_reg _ _ _ _ _ 19 19%bv eq_refl); exact H19).
  remember (EJ regs1 (x_regs c) 0 0 q4) as E0 eqn:HE0 in *.
  assert (HAG : env_agree 41 (EJ regs1 (x_regs c) 0 0 q4) E0) by (rewrite HE0; apply env_agree_refl).
  clear HE0.
  assert (KM : kept_out (rdW (x_W c) memc) (rdW (x_W c) memc) (sp0 + -48 - 2 * ESTACK) (sp0 + -48))
    by (intros a _ _; reflexivity).
  (* li a0,5 ; bne s3,a0 *)
  paj_run_tok RUN HS HJ SHOK RBspanJ; [awr_ok_tac |].
  pm_keep KM. pm_md.
  psrr_branch_tok RUN BR HS SHOK RBspanJ.
  { exfalso. rewrite (pm_ne_lit _ 19 (x_ntok c) 5 E19 ltac:(lia) ltac:(lia)), Hn5 in Hc.
    vm_compute in Hc. discriminate Hc. }
  clear Hc.
  (* the UBSan checks 0x8e234 / 0x8e240 (decided by tok's fact), the load8 check of tok + 32, ld s3, the
     arguments, to the strncmp call *)
  paj_run_tok RUN HS HJ SHOK RBspanJ; [awr_ok_tac |].
  pm_keep KM. pm_md.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msC end.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
  prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
  pmkst HS.
  assert (Ca0 : getr (ms_regs msC) 10 = w64 q4)
    by (rewrite Ra0, (pm_ew_agree _ _ _ 40 HAG ltac:(lia)), pm_ew40; reflexivity).
  assert (Ca1 : getr (ms_regs msC) 11 = w64 0x22900).
  { rewrite Ra1, (pm_img_atom E0 366 HEI ltac:(cbv; lia)). change 366%nat with (A_OBJ 125).
    rewrite HVO by (vm_compute; lia). reflexivity. }
  assert (Csp : spZ (ms_regs msC) = sp0 + -48) by (unfold spZ; rewrite Qsp, Usp; lia).
  assert (Cgp : getr (ms_regs msC) 3 = w64 (as_gp B))
    by (rewrite Qgp, (pm_ew_agree _ _ _ 3 HAG ltac:(lia)), (pm_ew_reg _ _ _ _ _ 3 3%bv eq_refl), Q3; exact Hgp).
  assert (Ctp : getr (ms_regs msC) 4 = w64 (as_tp B))
    by (rewrite Qtp, (pm_ew_agree _ _ _ 4 HAG ltac:(lia)), (pm_ew_reg _ _ _ _ _ 4 4%bv eq_refl), Q4; exact Htp).
  assert (KE : kept_out (rdW (x_W c) (x_mem c)) (rdW (x_W c) (ms_mem msC)) (sp0 - PIN_SET_WORDS_STK) sp0)
    by exact (kept_out_trans _ _ _ _ _ _ _ HK0 KM ltac:(lia) ltac:(lia)).
  destruct (psw_blk_ready B HB (x_ly c) (x_S c) (x_W c) (x_mem c) (ms_mem msC) _ (2 * ESTACK)
    (sp0 - PIN_SET_WORDS_STK) sp0 (ms_regs msC) q4 w4 (x_cb c) (x_ncb c) (proj1 HJ) KE ltac:(lia)
    ltac:(rewrite Csp; lia) ltac:(lia) Hcb Hcb4 Hce4 Hs4) as (Hx0 & Hsx & Hrx & Htx).
  destruct (psw_verdict_ready B HB (x_ly c) (x_S c) (x_W c) (x_mem c) (ms_mem msC) _ (2 * ESTACK)
    (sp0 - PIN_SET_WORDS_STK) sp0 (ms_regs msC) (proj1 HJ) (pp_ro B MT c HP) KE ltac:(lia)
    ltac:(rewrite Csp; lia) ltac:(lia)) as (Hy0 & Hsy & Hry & Hty).
  pose proof (psw_rom_kept B (x_W c) (x_mem c) (ms_mem msC) (sp0 - PIN_SET_WORDS_STK) sp0 (pp_rod B MT c HP) KE
    ltac:(lia)) as Hrom.
  assert (Hrx8 : aread_ok SEGS (2 * ESTACK) (x_W c) (ms_regs msC) (ms_mem msC) q4 (Z.min 8 (astr_len w4 + 1)))
    by (apply (pm_aread_ok_prefix _ _ _ _ _ _ _ Hrx); unfold astr_len; lia).
  (* the strncmp contract's `+ 8` band premises (RtString.v:128-132): tok[4] lies in the copy block (amem8_of_block),
     "verdict=" in .rodata (amem8_of_low) *)
  assert (AMx : amem_range q4 (astr_len w4 + 8))
    by (apply (amem8_of_block SEGS B LAWS _ _ _ _ _ (x_cb c) (x_ncb c) q4 (astr_len w4) HAR Hcb Hcb4); unfold astr_len; lia).
  assert (AMy : amem_range 0x22900 (astr_len Verbs.Lit.word_verdict + 8))
    by (apply amem8_of_low; [lia | apply Z.leb_le; vm_compute; reflexivity]).
  (* strncmp(tok[4], "verdict=", 8) *)
  eapply SRr_bind.
  { exact (aj_strncmp_at SEGS B LAWS pa_segs_low (CmdRecCells.cmd_cf_env SEGS B LAWS HB IMG) _ (STRNCMP fx)
      (x_W c) (ms_regs msC) (ms_mem msC)
      PIN_SET_WORDS_STK sp0 (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [] (x_ly c) (x_S c) _ 0
      q4 0x22900 8 w4 Verbs.Lit.word_verdict (-48) _ HJ Ca0 Ca1 Ra2 ltac:(lia) ltac:(lia) ltac:(lia) Csp eq_refl
      ltac:(lia) ltac:(lia) Cgp Ctp Rra ltac:(apply ret_ok_codeptr_v; [lia | reflexivity])
      Hsx Hsy Hrx8 AMx Hry AMy Htx Hty Hrom). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  assert (Hfr2' : kept_out (rdW (x_W c) (ms_mem msC)) (rdW (x_W c) mem2) (sp0 + -48 - 2 * ESTACK) (sp0 + -48))
    by (intros a Ha Hn; exact (Hfr2 a Ha Hn (fun F => F))).
  assert (KM2 : kept_out (rdW (x_W c) memc) (rdW (x_W c) mem2) (sp0 + -48 - 2 * ESTACK) (sp0 + -48))
    by exact (kept_out_trans _ _ _ _ _ _ _ KM Hfr2' ltac:(lia) ltac:(lia)).
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H (x_W c)) mem2) HP2 [0; 1]%nat HS2.
  match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (pm_region_kept _ _ _ _ 8 (x_tok c)); [exact Utok | intros a Ha; apply Hfr2; [lia | lia | tauto] | intros a Ha; lia].
    - apply (pm_region_kept _ _ _ _ 2 (sp0 - 48)); [exact Usp | intros a Ha; apply Hfr2; [lia | lia | tauto] | intros a Ha; lia]. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS SHOK. rename HS2 into HS. clear HJ KM. rename HJ2 into HJ. rename KM2 into KM.
  assert (E52 : ew (havoc E0 48 (map (getr regs2) CLOB)) 52 = getr regs2 10) by exact (pm_havoc_a0 E0 48 regs2).
  assert (HEI1 : img_env VAL A_LIM (havoc E0 48 (map (getr regs2) CLOB)))
    by (apply img_env_havoc; [exact HEI | apply Nat.leb_le; vm_compute; reflexivity]).
  assert (HAG1 : env_agree 41 (EJ regs1 (x_regs c) 0 0 q4) (havoc E0 48 (map (getr regs2) CLOB)))
    by (apply env_agree_havoc_ge; [lia | exact HAG]).
  remember (havoc E0 48 (map (getr regs2) CLOB)) as E1 eqn:HE1 in *. clear HE1 HEI HAG.
  assert (SHOK : sh_ok SEGS BxJ [] E1 (mrestrict (w_H (x_W c)) mem2)) by constructor.
  destruct (psw_verdict w4 (proj2 Hs4)) as (v & Hv & _ & Hvi).
  (* bnez a0 *)
  psrr_branch_tok RUN BR HS SHOK RBspanJ.
  + (* strncmp <> 0: the epilogue returns s2 = -902 (R4) *)
    rewrite (pm_ne0 _ 52 _ E52) in Hc.
    assert (Hnp : Verbs.has_prefix Verbs.Lit.word_verdict w4 = false).
    { destruct (Verbs.has_prefix Verbs.Lit.word_verdict w4) eqn:Hh; [|reflexivity]. exfalso.
      assert (H0 : getr regs2 10 = w64 0)
        by (apply Hcmp; rewrite Hv; f_equal; apply Hvi; first [reflexivity | exact Hh]).
      rewrite H0 in Hc. vm_compute in Hc. discriminate Hc. }
    assert (Hm : Verbs.pin_set_words_m (x_T c) (tl (x_tks c)) = Verbs.reject)
      by (rewrite Etks; cbn [tl]; exact (psw_m_bad4 (x_T c) u f w3 w4 Hnp)).
    assert (HEV0 : EV_PIN_SET_WORDS (x_R c) (x_T c) (tl (x_tks c)) = 0)
      by (unfold EV_PIN_SET_WORDS; rewrite Hm; reflexivity).
    paj_run_tok RUN HS HJ SHOK RBspanJ; [awr_ok_tac |].
    pm_keep KM. pm_md.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msR end.
    destruct (psw_aregs_leaf (x_regs c) regs1 0 0 q4 E1 _ (w_H (x_W c)) msR HS HAG1 ltac:(vm_compute; reflexivity)
      Q2 Q3 Q4 Qhi ltac:(lia)) as [RA1 HAREGS].
    prreg HS (10%bv : bv 5) R10.
    assert (H10 : getr (ms_regs msR) 10 = w64 Verbs.err_invalid_operation)
      by (rewrite R10, (pm_ew_agree _ _ _ 18 HAG1 ltac:(lia)), (pm_ew_reg _ _ _ _ _ 18 18%bv eq_refl); exact H18).
    eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    apply (psw_leaf_post B MT c (x_W c) (ms_regs msR) (ms_mem msR) _ (x_ly c) (x_S c) 0 Hra RA1 HAREGS HJ
      ltac:(rewrite HEV0; lia) mat').
    exact (psw_Q_reject B MT MTL c (ms_regs msR) (ms_mem msR) _ HP Hm
      (kept_out_trans _ _ _ _ _ _ _ HK0 KM ltac:(lia) ltac:(lia)) H10).
  + (* strncmp = 0: addi a3,s3,8 ; li a0,9 ; bgeu a3,a0 (the UBSan check 0x8e27c, decided by tok[4]'s fact) ; JOIN
       with the verdict tok[4] + 8 *)
    rewrite (pm_ne0 _ 52 _ E52) in Hc.
    assert (H0 : getr regs2 10 = w64 0).
    { apply pm_w0. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc. exact Hc. }
    assert (Hpre : Verbs.has_prefix Verbs.Lit.word_verdict w4 = true).
    { apply Hvi. apply Hcmp in H0. rewrite Hv in H0. injection H0 as H0. exact H0. }
    assert (H8w : (8 <= length w4)%nat).
    { unfold Verbs.has_prefix in Hpre. apply andb_prop in Hpre as [Hle _]. apply Nat.leb_le in Hle.
      rewrite psw_verdict_len in Hle. exact Hle. }
    paj_run_to_tok RUNTO HS HJ SHOK RBspanJ PSW_JOIN; [awr_ok_tac |].
    pm_keep KM. pm_md.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msJ end.
    prreg HS (13%bv : bv 5) R13.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ pm_keep_regs HS (pm_agree32 _ _ _ _ _ _ HAG1)
      ltac:(vm_compute; reflexivity)) as HKR.
    cbn [ms_regs restrict mkst] in HKR.
    pmkst HS.
    pm_join FJ.
    exists q1, q2, p3, u, f, w3, (Some (skipn 8 w4)), (q4 + 8).
    split; [pm_cut HJ HK0 KM HSV HKR Q2 Q3 Q4 Q8 Q9 Q20 Qhi|].
    split; [rewrite R13, (pm_ew_agree _ _ _ 40 HAG1 ltac:(lia)), pm_ew40, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Eptrs; reflexivity|].
    split; [rewrite Eptrs; reflexivity|].
    split; [rewrite Eptrs; reflexivity|].
    split; [rewrite Etks; reflexivity|].
    split; [rewrite Etks; reflexivity|].
    split; [rewrite Etks; reflexivity|].
    split; [rewrite Etks; cbn [tl]; exact (psw_m_len4 (x_T c) u f w3 w4 HlenT Hdash Hpre)|].
    right. exists q4, w4.
    split; [rewrite Eptrs; reflexivity|]. split; [rewrite Etks; reflexivity|].
    split; [exact H8w|]. split; reflexivity.
Qed.
End e.
End f.
End d.
