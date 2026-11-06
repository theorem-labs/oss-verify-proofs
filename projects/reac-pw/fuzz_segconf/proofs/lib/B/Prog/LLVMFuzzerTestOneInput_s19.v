(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D1p56.v, with its module paths and module names changed; 1017 of its 1069 lines of code are new or changed and 689 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (asan-ubsan, pin c3796c0b38f3): segment S10 of
   LLVMFuzzerTestOneInput's walk (0x84dc0): lt_seg_S10 : lt_seg_S10_stmt (LTA_K85868 -> LT_K856f4_stmt), statement in
   LLVMFuzzerTestOneInput_defs.v.
   0x856f4 .. 0x856fc: a0 = c, a1 = m, jal check_refusals (the contract check_refusals_c at BASE + AF_check_refusals).
   0x85700 .. 0x857a4: SH(m + 0x23ac) to 160(s1), check 20 (n_kept's shadow), n_kept <= 0 out to K85868, else the
   loop's set-up: ~(m + 0x238c), ~(m + 0x200c), ~(c + 0x2e88) to 128 / 136 / 144(s1), c & 7 = 0 to 152(s1) (the
   alignment trap 0x857ac reads it), the slow-path bounds to 104 / 112(s1).
   The loop, turn i (0x857a8 .. 0x85838): trap 0x857ac (152(s1) = 0), check 21 (n_refusals' shadow), i < n_refusals
   (refuted to exit: check_refusals gives n_refusals = n_kept > i), the pointer-overflow traps 0x857c4 (~(c + 0x2e88) <u
   200 i) and 0x857d0 (~(m + 0x200c) <u 112 i), jal check_address (refusal[i], kept[i]); the traps 0x857e8 (s11 =
   112 i - 896 = 0) and 0x857f0 (~(m + 0x238c) <u 4 i), check 22 (kept_knock[i]'s shadow), jal check_knock_refused
   (refusal[i], kept_knock[i]); check 23 (n_kept's shadow), i += 1, blt i, n_kept to the next turn or out to K85868.
   Each UBSan trap branch is refuted by the values of the blocks (B-DELTA.md section 0: AR_blocks_law's bounds,
   c, m >= 4096 and below the allocation ceiling) and of i < n_kept <= 8. Every ASan check passes by the shadow of
   the live blocks c and m (the seeds' shadow entries). No runtime entry is reached but the three program calls.
   Adopted from image A's twin (image A's S10 commit 5d411a135ac8, lib/A/Prog/LLVMFuzzerTestOneInput_s19.v):
   the loop's decomposition (the body's two return points s19_PA / s19_PK, s19_stepCA / s19_stepCK, the vacuous
   turns and the induction s19_loop), s19_regs_ok_set, s19_shent, s19_blocks, s19_model, s19_pre_ca, s19_pre_ck,
   s19_rreg, s19_awr_ro, s19_pres / s19_cs, renamed to image B's registers, slots and pcs. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import check_refusals_c check_address_c
check_knock_refused_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c
LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_s19k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition s19a_rsl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 168 200 0 0 [YP09.mkChunk 168 (CVal 8 (SOff 32 0)); YP09.mkChunk 192 (CVal 8 (SOff 33 0))].
Definition s19a_ss : sstate := mkSS LO_K856f4 sr_atoms [s19a_rsl] None (mkFacts [] [] []).
(* the set-up's seed at 0x85700: atoms 32 c, 33 m, 34 the shadow base, 35 n_kept; the two windows of s1 slots it
   writes (104 .. 119, 128 .. 167), the slots it reads, and n_kept *)
Definition s19b_rw1 : YP09.region := YP09.mkRegion (Some 9%nat) 104 120 104 120 [].
Definition s19b_rw2 : YP09.region := YP09.mkRegion (Some 9%nat) 128 168 128 168 [].
Definition s19b_rsl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 168 224 0 0
    [YP09.mkChunk 168 (CVal 8 (SOff 32 0)); YP09.mkChunk 192 (CVal 8 (SOff 33 0));
     YP09.mkChunk 200 (CVal 8 (SOff 34 0)); YP09.mkChunk 216 (CVal 8 (SOff 33 8192))].
Definition s19b_rm : YP09.region := YP09.mkRegion (Some 33%nat) 9132 9136 0 0 [YP09.mkChunk 9132 (CVal 4 (SOff 35 0))].
Definition s19b_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 4);
           (33%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 4); (34%nat, mkAF SB SB 0); (35%nat, mkAF 0 8 0)] [] [].
Definition s19b_ss : sstate := mkSS LO_CR_RA sr_atoms [s19b_rw1; s19b_rw2; s19b_rsl; s19b_rm] None s19b_facts.



(* ---- the loop's symbolic state, at its head 0x857a8 and at its two return points 0x857e4 / 0x85814: every
   register its own atom but s3 = SH(s6) as the code formed it; atom 32 the shadow base (the word at 200(s1)),
   33 n (n_kept = n_refusals), 34 kept_knock[i], 35 &m->kept_knock[i] (the alias of s10 + s5); the slots 128 .. 160
   the set-up wrote and 200(s1); n_refusals at s6, n_kept at s9, kept_knock[i] at atom 35; the shadow entries of the
   8 bytes from s6, s9 and atom 35 ---- *)
Definition s19_shx (a : nat) (d : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff a d) (SLit 3)) (SOff 32 0).
Definition s19L_rf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 128 208 0 0
    [YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 26 0) (SLit (-1))));
     YP09.mkChunk 136 (CVal 8 (SAlu ALU_XOR (SOff 26 (-896)) (SLit (-1))));
     YP09.mkChunk 144 (CVal 8 (SAlu ALU_XOR (SOff 18 0) (SLit (-1))));
     YP09.mkChunk 152 (CVal 8 (SLit 0));
     YP09.mkChunk 160 (CVal 8 (s19_shx 25 0));
     YP09.mkChunk 200 (CVal 8 (SOff 32 0))].
Definition s19L_rr : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition s19L_rn : YP09.region := YP09.mkRegion (Some 25%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition s19L_rk : YP09.region := YP09.mkRegion (Some 35%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))].
Definition s19L_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (21%nat, mkAF 0 28 0);
           (22%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (23%nat, mkAF 0 1400 0); (24%nat, mkAF 0 7 0);
           (25%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (26%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0);
           (27%nat, mkAF (2 ^ 64 - 896) (2 ^ 64 - 112) 0); (32%nat, mkAF SB SB 0); (33%nat, mkAF 1 8 0);
           (34%nat, mkAF 0 1 0); (35%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0)] []
    [(SAlu ALU_ADD (SOff 26 0) (SOff 21 0), SOff 35 0)].
Definition s19L_regs : list sv := sr_set sr_atoms 19%bv (s19_shx 22 0).
Definition ss_L (pc : Z) : sstate := mkSS pc s19L_regs [s19L_rf; s19L_rr; s19L_rn; s19L_rk] None s19L_facts.
Definition s19_SHL : list shent := [mkSHE 22 0 8; mkSHE 25 0 8; mkSHE 35 0 8].

(* the loop's registers at turn i (all callee-saved) *)
Definition s19_lr (regs : bvmap 5 word) (c m : Z) (i : nat) : Prop :=
  getr regs 18 = w64 (c + 11912) /\ getr regs 19 = w64 (shadow_addr (c + 13512)) /\
  getr regs 21 = w64 (4 * Z.of_nat i) /\ getr regs 22 = w64 (c + 13512) /\ getr regs 23 = w64 (200 * Z.of_nat i) /\
  getr regs 24 = w64 (Z.of_nat i) /\ getr regs 25 = w64 (m + 9132) /\ getr regs 26 = w64 (m + 9100) /\
  getr regs 27 = w64 (112 * Z.of_nat i - 896).
Lemma s19_pres : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac s19_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Lemma s19_lr_pres : forall regs regs' c m i, aregs_preserved regs regs' -> s19_lr regs c m i -> s19_lr regs' c m i.
Proof.
intros regs regs' c m i HP (R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
unfold s19_lr.
rewrite (s19_pres regs regs' 18 HP), (s19_pres regs regs' 19 HP), (s19_pres regs regs' 21 HP),
  (s19_pres regs regs' 22 HP), (s19_pres regs regs' 23 HP), (s19_pres regs regs' 24 HP),
  (s19_pres regs regs' 25 HP), (s19_pres regs regs' 26 HP), (s19_pres regs regs' 27 HP) by s19_cs.
repeat split; assumption.
Qed.

(* a register set to a value its expression denotes (image A's twin s19_regs_ok_set, image A's S10 commit
   5d411a135ac8, LLVMFuzzerTestOneInput_s19.v:217-224) *)
Lemma s19_regs_ok_set : forall E sr regs (r : bv 5) e, regs_ok E sr regs -> bv_eqb r 0 = false ->
  getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'. specialize (Hr r'). unfold sr_set. rewrite Hr0.
unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
Qed.
Lemma s19_denot_of_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v <-. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma s19_denot_off_w : forall E n v o, ew E n = w64 v -> sv_denot E (SOff n o) = w64 (v + o).
Proof.
intros E n v o H. cbn [sv_denot]. rewrite H. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma s19_val_rng4 : forall (rd : reader) a v, sa_val rd a 4 v -> 0 <= v < 2 ^ 32 -> 0 <= v < 2 ^ 32.
Proof. intros; assumption. Qed.

(* a register of a symbolic state, its value as the run left it (image A's twin s19_rreg,
   LLVMFuzzerTestOneInput_s19.v:274-284) *)
Ltac s19_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition s19b_E (regs : bvmap 5 word) (c m nk : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [c; m; SB; nk])).
Definition s19L_E (regs : bvmap 5 word) (n kn kp : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [SB; n; kn; kp])).

(* the shadow entry of [p + lo, p + hi), inside a live heap block whose shadow is addressable (image A's twin
   s19_shent, LLVMFuzzerTestOneInput_s19.v:239-254) *)
Lemma s19_shent : forall (W : world SEGS) mem E (mt : nat) b n p lo hi,
  range_addressable (rdW W mem) SHADOW_OFF b n -> in_app b n ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E mt = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
  b <= p + lo -> p + hi <= b + n -> lo < hi ->
  shent_ok SEGS (SOff 32 0) E (mrestrict (w_H W) mem) (mkSHE mt lo hi).
Proof.
intros W mem E mt b n p lo hi Hra Happ E32 Em Hp Hlo Hhi Hlh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (shent_ok_of_range SEGS (w_H W) mem E (SOff 32 0) mt b n p lo hi Hra).
- apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF. lia.
- apply (U_atom E mt p Em Hp).
- exact Hlo.
- exact Hhi.
- intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ.
  unfold SHADOW_OFF. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis HCR : forall fx0 : YK11.FPState, @check_refusals_contract fx0 rc SK SEGS B (BASE + AF_check_refusals)
  STK_check_refusals.

Hypothesis HCA : forall fx0 : YK11.FPState,
  @check_address_contract fx0 rc SK SEGS B (BASE + AF_check_address) STK_check_address RLO_A RHI_A.
Hypothesis HCK : forall fx0 : YK11.FPState,
  @check_knock_refused_contract fx0 rc SK SEGS B (BASE + AF_check_knock_refused) STK_check_knock_refused
    RLO_A RHI_A seg_litA_fz gotwA guardA.


(* the set-up's seed: the state at 0x85700 is an instance of s19b_ss *)
Lemma s19b_seed : forall cx ly S W regs mem md k acc c m,
  lt_base B MT cx -> s19_inv B MT cx ly S W regs mem md k acc c m ->
  st_ok_pi SEGS VAL (s19b_E regs c m (Z.of_nat (length (SegModel.mc_kept (x_mcF cx))))) s19b_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_CR_RA)) mem (seg_rom SEGS))).
Proof.
intros cx ly S W regs mem md k acc c m HBASE HINV.
pose proof HINV as (HCORE & HBc & HBm & SLOTS & HCM).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & SAVED & HD0 & HD8 & HD16 & HFLW & S200 & FSH & S184) & _).
destruct (s19_frame_at B MT cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & STKc & S1c & SP47 & SP16 & S132 & SPtop).
assert (S1r : x_sp0 cx - 368 <= x_s1 cx <= x_sp0 cx - 352) by (destruct S1c as [Eq|Eq]; rewrite Eq; lia).
unfold STK_LLVMFuzzerTestOneInput in STKc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (s19_inv_blk B MT cx ly S W _ _ md k acc c m HINV)
  as ((Hc0 & Hc16 & Hch & Hca & Hc4 & Hcc) & (Hm0 & Hm16 & Hmh & Hma & Hm4 & Hmc)).
unfold seg_spec.SEG_C_SIZE in Hcc. unfold seg_spec.SEG_M_SIZE in Hmc.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
destruct HCM as [_ HMC]. destruct (s19_nkept_val _ _ _ HMC) as (NKV & NK8).
change (seg_spec.seg_mc (x_run cx)) with (x_mcF cx) in NKV, NK8.
pose proof (SLOTS 168 c ltac:(unfold LT_LC; cbn [In app]; repeat (first [left; reflexivity | right]))) as SL168.
pose proof (SLOTS 192 m ltac:(unfold LT_LC; cbn [In app]; repeat (first [left; reflexivity | right]))) as SL192.
pose proof (SLOTS 216 (m + seg_spec.MC_N) ltac:(unfold LT_LC; cbn [In app]; repeat (first [left; reflexivity | right])))
  as SL216.
set (nk := Z.of_nat (length (SegModel.mc_kept (x_mcF cx)))) in *.
set (E := s19b_E regs c m nk).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold s19b_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (map (Z_to_bv 64) [c; m; SB; nk]) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold s19b_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth map] in E32, E33, E34, E35. clear EX.
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = m) by (rewrite E33; apply unsigned_lit_small; lia).
assert (RG : regs_ok E sr_atoms regs) by (subst E; unfold s19b_E; apply regs_ok_Eimg_Ereg).
clearbody E.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact RG.
- vm_compute. reflexivity.
- unfold s19b_ss, s19b_rw1, s19b_rw2, s19b_rsl, s19b_rm. cbn [ss_mem].
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U9, ?U33.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HPRES. unfold STK_LLVMFuzzerTestOneInput. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HPRES. unfold STK_LLVMFuzzerTestOneInput. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (s19_word_chunk W mem E (SOff 32 0) (x_s1 cx) 168 c SL168). rewrite (s19_denot_off E 32 c 0 E32) by lia.
      rewrite Z.add_0_r. reflexivity.
    * apply (s19_word_chunk W mem E (SOff 33 0) (x_s1 cx) 192 m SL192). rewrite (s19_denot_off E 33 m 0 E33) by lia.
      rewrite Z.add_0_r. reflexivity.
    * apply (s19_word_chunk W mem E (SOff 34 0) (x_s1 cx) 200 SHADOW_OFF S200).
      rewrite (s19_denot_off E 34 SB 0 E34) by (unfold SB; lia). rewrite Z.add_0_r. reflexivity.
    * apply (s19_word_chunk W mem E (SOff 33 8192) (x_s1 cx) 216 (m + seg_spec.MC_N) SL216).
      rewrite (s19_denot_off E 33 m 8192 E33) by lia. reflexivity.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (s19_u32_chunk W mem E (SOff 35 0) m 9132 nk NKV); [unfold nk; lia|].
    rewrite (s19_denot_off E 35 nk 0 E35) by (unfold nk; lia). rewrite Z.add_0_r. reflexivity.
- apply pairwise_disjoint_of_extents. unfold extent_of_region, s19b_ss, s19b_rw1, s19b_rw2, s19b_rsl, s19b_rm.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s19b_ss s19b_facts ss_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U33, E32, E34, E35, !unsigned_lit_small by (unfold SB, nk; lia).
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, nk. repeat match goal with |- _ /\ _ => split end. all: try exact I. all: try lia.
Qed.
(* ---- 0x85700 .. 0x857a4: m + 0x23ac, its shadow address to 160(s1), check 20, n_kept; n_kept <= 0 goes out to
   K85868, else the loop's set-up (the complements to 128 / 136 / 144, C & 7 = 0 to 152, the slow-path bounds to
   104 / 112) to the head of turn 0 ---- *)
Lemma s19_setup : LTA_K85868 B MT -> K857a8_stmt B MT 0 ->
  forall cx ly S W regs mem md k acc c m,
  lt_base B MT cx -> sa_frm0 -> s19_inv B MT cx ly S W regs mem md k acc c m ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_CR_RA)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros HX HL0 cx ly S W regs mem md k acc c m HBASE HFRM HINV.
pose proof HINV as (HCORE & HBc & HBm & SLOTS & HCM).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & SAVED & HD0 & HD8 & HD16 & HFLW & S200 & FSH & S184) & _ & _ & HBUD).
destruct (s19_frame_at B MT cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & STKc & S1c & SP47 & SP16 & S132 & SPtop).
assert (S1r : x_sp0 cx - 368 <= x_s1 cx <= x_sp0 cx - 352) by (destruct S1c as [Eq|Eq]; rewrite Eq; lia).
unfold STK_LLVMFuzzerTestOneInput in STKc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (s19_inv_blk B MT cx ly S W _ _ md k acc c m HINV)
  as ((Hc0 & Hc16 & Hch & Hca & Hc4 & Hcc) & (Hm0 & Hm16 & Hmh & Hma & Hm4 & Hmc)).
unfold seg_spec.SEG_C_SIZE in Hcc. unfold seg_spec.SEG_M_SIZE in Hmc.
pose proof HCM as [HRC HMC]. destruct (s19_nkept_val _ _ _ HMC) as (NKV & NK8).
change (seg_spec.seg_mc (x_run cx)) with (x_mcF cx) in NKV, NK8.
pose proof (s19b_seed cx ly S W regs mem md k acc c m HBASE HINV) as HS.
set (nk := Z.of_nat (length (SegModel.mc_kept (x_mcF cx)))) in *.
set (E := s19b_E regs c m nk) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s19b_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold s19b_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (map (Z_to_bv 64) [c; m; SB; nk]) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold s19b_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth map] in E32, E33, E34, E35. clear EX.
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (U34 : U E (SOff 34 0) = SHADOW_OFF) by (rewrite (U_atom E 34 SB E34) by (unfold SB; lia); reflexivity).
assert (U33k : forall o, 0 <= o <= 9236 -> U E (SOff 33 o) = m + o)
  by (intros o Ho; rewrite (U_atom_off E 33 m o E33) by lia; reflexivity).
assert (U32k : forall o, 0 <= o <= 16616 -> U E (SOff 32 o) = c + o)
  by (intros o Ho; rewrite (U_atom_off E 32 c o E32) by lia; reflexivity).
assert (U9' : bv_unsigned (ew E 9) = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by lia.
pose proof HBm as (Hinm & _).
assert (AWRE : forall E0, bv_unsigned (ew E0 9) = x_sp0 cx + (x_s1 cx - x_sp0 cx) ->
  awr_ok SEGS B E0 (ss_mem s19b_ss) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)]).
{ intros E0 U90. unfold s19b_ss. cbn [ss_mem].
  eapply awr_ok_cons_stack_off; [reflexivity | exact U90 | unfold STK_LLVMFuzzerTestOneInput; cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off; [reflexivity | exact U90 | unfold STK_LLVMFuzzerTestOneInput; cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 34 0) [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
set (Zs := fun a => x_s1 cx + 104 <= a < x_s1 cx + 120 \/ x_s1 cx + 128 <= a < x_s1 cx + 168).
paj_run_tok RUN HS HJ SHOK s19_span.
{ cbn [ms_mem mkst]. rewrite (U33k 9132) by lia.
  apply (obl_of_block SEGS B LAWS ly S W mem md E (SOff 34 0) (m + 9132) 4 m seg_spec.SEG_M_SIZE (proj1 HJ) Hinm U34);
  unfold req_size, seg_spec.SEG_M_SIZE; cbn; lia. }
{ exact (AWRE E U9'). }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ Zs HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. unfold Zs.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val ew ewset] in Hrr; rewrite ?U9 in Hrr; lia|]).
  destruct Hin'. }
clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK s19_span.
- (* n_kept <= 0: out of S10 to K85868 *)
  paj_run_to_tok RUNTO HS HJ SHOK s19_span LO_K85868.
  { apply (s19_awr_skel SEGS B _ (ss_mem s19b_ss)); [vm_compute; reflexivity | apply AWRE; cbn [ew ewset Nat.eqb]; exact U9']. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a).
  { intros a Ha Hn. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ Zs HFr); [|exact Ha | exact Hn].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. unfold Zs.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?U9 in Hrr; lia|]).
    destruct Hin'. }
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  pmkst HS.
  assert (HINV2 : s19_inv B MT cx ly S W (ms_regs ms) (ms_mem ms) mdv2 k acc c m).
  { apply (s19_inv_xfer B MT cx ly S W regs mem md k acc c m ly S W (ms_regs ms) (ms_mem ms) mdv2 HBASE HINV HJ
      P2 P3 P4 P8 P9).
    - intros a Ha Hz. rewrite (K2 a Ha), (K1 a Ha); [reflexivity | |];
        unfold Zs; unfold s19_kz in Hz; lia.
    - apply Permutation_refl.
    - exact (proj1 (proj2 (proj2 (proj2 HBUD)))). }
  destruct HINV2 as (HC2 & HBc2 & HBm2 & SL2 & HCM2).
  exact (HX fx cx ly S W (ms_regs ms) (ms_mem ms) mdv2 k acc c m HBASE HFRM HC2 HBc2 HBm2 SL2 HCM2).
- (* n_kept > 0: the loop's set-up to the head of turn 0 *)
  assert (Hnk : 0 < nk).
  { rewrite (s19_br_ge _ _ _ 0 nk) in Hc;
      [ | reflexivity | rewrite (s19_denot_off _ 35 nk 0) by (first [cbn [ew ewset Nat.eqb]; exact E35 | unfold nk; lia]);
          rewrite Z.add_0_r; reflexivity | lia | unfold nk; lia].
    apply negb_false_iff, Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s19_span LO_K857a8.
  { apply (s19_awr_skel SEGS B _ (ss_mem s19b_ss)); [vm_compute; reflexivity | apply AWRE; cbn [ew ewset Nat.eqb]; exact U9']. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a).
  { intros a Ha Hn. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ Zs HFr); [|exact Ha | exact Hn].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. unfold Zs.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?U9 in Hrr; lia|]).
    destruct Hin'. }
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    assert (G32 : ew E2 32 = Z_to_bv 64 c) by (cbn [ew ewset Nat.eqb]; exact E32);
    assert (G33 : ew E2 33 = Z_to_bv 64 m) by (cbn [ew ewset Nat.eqb]; exact E33);
    assert (G34 : ew E2 34 = Z_to_bv 64 SB) by (cbn [ew ewset Nat.eqb]; exact E34);
    assert (G9 : bv_unsigned (ew E2 9) = x_s1 cx) by (cbn [ew ewset Nat.eqb]; exact U9) end.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
  destruct RG as (_ & _ & _ & RGc). cbn [YP09.r_base base_val YP09.r_chunks] in RGc. rewrite G9 in RGc.
  assert (LSL : lt_slots cx (rdW W (ms_mem ms)) (s19_lslots c m)).
  { intros o v Hin. unfold s19_lslots in Hin. cbn [In] in Hin.
    destruct Hin as [Hq | [Hq | [Hq | [Hq | [Hq | []]]]]]; injection Hq as <- <-.
    - apply (s19_rd_chunk8 _ _ _ (x_s1 cx) 128 _ (SAlu ALU_XOR (SOff 33 9100) (SLit (-1))) _ _ RGc);
        [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | | unfold lt_not; lia].
      rewrite denot_lit_U, (s19_U_not _ 33 m 9100 G33) by lia. reflexivity.
    - apply (s19_rd_chunk8 _ _ _ (x_s1 cx) 136 _ (SAlu ALU_XOR (SOff 33 8204) (SLit (-1))) _ _ RGc);
        [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | | unfold lt_not; lia].
      rewrite denot_lit_U, (s19_U_not _ 33 m 8204 G33) by lia. reflexivity.
    - apply (s19_rd_chunk8 _ _ _ (x_s1 cx) 144 _ (SAlu ALU_XOR (SOff 32 11912) (SLit (-1))) _ _ RGc);
        [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | | unfold lt_not; lia].
      rewrite denot_lit_U, (s19_U_not _ 32 c 11912 G32) by lia. reflexivity.
    - apply (s19_rd_chunk8 _ _ _ (x_s1 cx) 152 _ (SLit 0) _ _ RGc);
        [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | lia].
    - apply (s19_rd_chunk8 _ _ _ (x_s1 cx) 160 _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 9132) (SLit 3)) (SOff 34 0)) _ _ RGc);
        [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | |
         unfold shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia].
      rewrite denot_lit_U, (s19_U_sh _ 33 34 m 9132 G33 G34) by lia. reflexivity. }
  s19_prraw HS (18%bv : bv 5) P18. s19_prraw HS (19%bv : bv 5) P19. s19_prraw HS (21%bv : bv 5) P21.
  s19_prraw HS (22%bv : bv 5) P22. s19_prraw HS (23%bv : bv 5) P23. s19_prraw HS (24%bv : bv 5) P24.
  s19_prraw HS (25%bv : bv 5) P25. s19_prraw HS (26%bv : bv 5) P26. s19_prraw HS (27%bv : bv 5) P27.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  pmkst HS.
  assert (HINV2 : s19_inv B MT cx ly S W (ms_regs ms) (ms_mem ms) mdv2 k acc c m).
  { apply (s19_inv_xfer B MT cx ly S W regs mem md k acc c m ly S W (ms_regs ms) (ms_mem ms) mdv2 HBASE HINV HJ
      P2 P3 P4 P8 P9).
    - intros a Ha Hz. rewrite (K2 a Ha), (K1 a Ha); [reflexivity | |];
        unfold Zs; unfold s19_kz in Hz; lia.
    - apply Permutation_refl.
    - exact (proj1 (proj2 (proj2 (proj2 HBUD)))). }
  apply (HL0 cx ly S W (ms_regs ms) (ms_mem ms) mdv2 k acc c m HBASE HFRM ltac:(unfold nk in Hnk; lia) HINV2 LSL).
  + apply (s19_reg_U _ _ _ _ _ P18). rewrite (U_atom_off _ 32 c 11912 G32) by lia. reflexivity.
  + apply (s19_reg_U _ _ _ _ _ P19). rewrite (s19_U_sh _ 32 34 c 13512 G32 G34) by lia. reflexivity.
  + apply (s19_reg_U _ _ _ _ _ P21). rewrite U_SLit. reflexivity.
  + apply (s19_reg_U _ _ _ _ _ P22). rewrite (U_atom_off _ 32 c 13512 G32) by lia. reflexivity.
  + apply (s19_reg_U _ _ _ _ _ P23). rewrite U_SLit. reflexivity.
  + apply (s19_reg_U _ _ _ _ _ P24). rewrite U_SLit. reflexivity.
  + apply (s19_reg_U _ _ _ _ _ P25). rewrite (U_atom_off _ 33 m 9132 G33) by lia. reflexivity.
  + apply (s19_reg_U _ _ _ _ _ P26). rewrite (U_atom_off _ 33 m 9100 G33) by lia. reflexivity.
  + rewrite P27. cbn [sv_denot]. unfold w64. apply Z_to_bv64_eq_mod. reflexivity.
Qed.

Lemma s19_head : LTA_K85868 B MT -> K857a8_stmt B MT 0 -> LT_K856f4_stmt B MT.
Proof.
intros HX HL0. unfold LT_K856f4_stmt.
intros cx ly S W regs mem md k acc c m HBASE HFRM HCORE HBc HBm SLOTS HCM.
assert (HINV : s19_inv B MT cx ly S W regs mem md k acc c m) by (split; [exact HCORE | split; [exact HBc | split; [exact HBm | split; [exact SLOTS | exact HCM]]]]).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & _) & _ & _ & HBUD).
destruct (s19_frame_at B MT cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & STKc & S1c & SP47 & SP16 & S132 & SPtop).
assert (S1r : x_sp0 cx - 368 <= x_s1 cx <= x_sp0 cx - 352) by (destruct S1c as [Eq|Eq]; rewrite Eq; lia).
unfold STK_LLVMFuzzerTestOneInput in STKc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (SLOTS 168 c ltac:(unfold LT_LC; cbn [In app]; repeat (first [left; reflexivity | right]))) as SL168.
pose proof (SLOTS 192 m ltac:(unfold LT_LC; cbn [In app]; repeat (first [left; reflexivity | right]))) as SL192.
set (E := Eimg (Ereg regs [Z_to_bv 64 c; Z_to_bv 64 m; Z_to_bv 64 SB])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 c)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 m)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E s19a_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K856f4)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [s19a_rsl YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    + apply (s19_word_chunk W mem E (SOff 32 0) (x_s1 cx) 168 c SL168).
      cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + apply (s19_word_chunk W mem E (SOff 33 0) (x_s1 cx) 192 m SL192).
      cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
assert (SHOK : sh_ok SEGS (SOff 34 0) [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
clearbody E.
unfold cfg_at. change (w64 (BASE + LO_K856f4)) with (Z_to_bv 64 (BASE + LO_K856f4)).
paj_run_tok RUN HS HJ SHOK s19_span.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]). destruct Hin'. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9. rewrite E32 in P10. rewrite E33 in P11.
pmkst HS.
rewrite (SIGP SS_check_refusals ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_refusals) with AF_check_refusals by (vm_compute; reflexivity).
assert (HINV1 : s19_inv B MT cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m).
{ apply (s19_inv_xfer B MT cx ly S W regs mem md k acc c m ly S W (ms_regs ms) (ms_mem ms) mdv HBASE HINV HJ
    P2 P3 P4 P8 P9).
  - intros a Ha _. exact (K1 a Ha).
  - apply Permutation_refl.
  - exact (proj1 (proj2 (proj2 (proj2 HBUD)))). }
destruct (s19_inv_blk B MT cx ly S W _ _ mdv k acc c m HINV1)
  as ((Hc0 & Hc16 & Hch & Hca & Hc4 & Hcc) & (Hm0 & Hm16 & Hmh & Hma & Hm4 & Hmc)).
pose proof (s19_inv_nev B MT cx ly S W _ _ mdv k acc c m HBASE HINV1) as HNEV.
pose proof (s19_checks (x_pl cx)) as (HCRf & HKA).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
assert (Hc64 : 0 <= c < 2 ^ 64) by (unfold seg_spec.SEG_C_SIZE in Hcc; lia).
assert (Hm64 : 0 <= m < 2 ^ 64) by (unfold seg_spec.SEG_M_SIZE in Hmc; lia).
apply (s19_prog_call B MT MTFL STK_check_refusals (BASE + AF_check_refusals) cx ly S W (ms_regs ms) (ms_mem ms) mdv
  k acc c m (getr (ms_regs ms) 1) HBASE HINV1 ltac:(unfold STK_check_refusals; lia) eq_refl).
- rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite P1. rewrite unsigned_lit_small; lia.
- intros ch HPRE1. pose proof HINV1 as (_ & _ & _ & _ & (HRC & HMC)).
  exact (HCR fx ly S W (ms_regs ms) (ms_mem ms) mdv ch c m _ _ HPRE1 P10 Hc64 P11 Hm64
    (conj Hc0 (conj Hc16 (conj HRC (conj Hch (conj Hca (conj Hm0 (conj Hm16 (conj HMC (conj Hmh (conj Hma HCRf))))))))))
    ltac:(unfold EV_check_refusals; lia)).
- intros W2 ly2 S2 regs2 mem2 md2 HINV2 HP2 KK2. rewrite P1.
  exact (s19_setup HX HL0 cx ly2 S2 W2 regs2 mem2 md2 k acc c m HBASE HFRM HINV2).
Qed.

(* the two harness blocks at a point of the segment: where they lie, apart, their shadow (image A's twin
   s19_blocks, LLVMFuzzerTestOneInput_s19.v:945-961) *)
Lemma s19_blocks : forall cx ly S W regs mem md k acc c m, s19_inv B MT cx ly S W regs mem md k acc c m ->
  4096 <= c /\ c + seg_spec.SEG_C_SIZE <= alloc_ceiling /\ 4096 <= m /\ m + seg_spec.SEG_M_SIZE <= alloc_ceiling /\
  (c + seg_spec.SEG_C_SIZE <= m \/ m + seg_spec.SEG_M_SIZE <= c) /\
  range_addressable (rdW W mem) SHADOW_OFF c seg_spec.SEG_C_SIZE /\ in_app c seg_spec.SEG_C_SIZE /\
  range_addressable (rdW W mem) SHADOW_OFF m seg_spec.SEG_M_SIZE /\ in_app m seg_spec.SEG_M_SIZE.
Proof.
intros cx ly S W regs mem md k acc c m
  (((HJ & _) & _ & HBL & _) & (HinC & _ & _ & (_ & _ & _ & HraC & _)) & (HinM & _ & _ & (_ & _ & _ & HraM & _)) & _).
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ c _ HAR HinC) as (_ & Hc4 & Hcc & Hca & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ m _ HAR HinM) as (_ & Hm4 & Hmc & Hma & _).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HBL) as Hd.
unfold block_rng, zdisjoint in Hd. cbn [fst snd] in Hd.
change (req_size seg_spec.SEG_C_SIZE) with 16616 in *. change (req_size seg_spec.SEG_M_SIZE) with 9236 in *.
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj HraC (conj Hca (conj HraM Hma)))))))); lia.
Qed.

(* the model's two refusal checks on the payload's run, and n_refusals = n_kept (image A's twin s19_model) *)
Lemma s19_model : forall cx : lcx,
  SegModel.check_refusals (x_rcF cx) (x_mcF cx) = true /\
  SegModel.check_kept_all (SegModel.rc_refusal (x_rcF cx)) (SegModel.mc_kept (x_mcF cx)) = true /\
  length (SegModel.rc_refusal (x_rcF cx)) = length (SegModel.mc_kept (x_mcF cx)).
Proof.
intros cx. destruct (s19_checks (x_pl cx)) as [H1 H2]. unfold x_rcF, x_mcF, x_run.
split; [exact H1|]. split; [exact H2|]. exact (s19_nref_eq _ _ H1).
Qed.

(* check_address's pre at turn i of the loop: refusal[i] of c, kept[i] of m (image A's twin s19_pre_ca,
   LLVMFuzzerTestOneInput_s19.v:782-813, over this walk's encoding lemmas) *)
Lemma s19_pre_ca : forall cx ly S W regs mem md k acc c m i, s19_inv B MT cx ly S W regs mem md k acc c m ->
  (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  check_address_pre B ly S (rdW W mem) (c + 11912 + 200 * Z.of_nat i) (m + 8204 + 112 * Z.of_nat i)
    (nth i (SegModel.rc_refusal (x_rcF cx)) []) (fst (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))).
Proof.
intros cx ly S W regs mem md k acc c m i HINV Hi.
pose proof HINV as (_ & (HinC & _ & _ & HaC) & (HinM & _ & _ & HaM) & _ & Hrc & Hmc).
change (sa_rconf (rdW W mem) c (x_rcF cx)) in Hrc. change (sa_mconf (rdW W mem) m (x_mcF cx)) in Hmc.
destruct (s19_model cx) as (_ & Mka & Mlen).
assert (Hir : (i < length (SegModel.rc_refusal (x_rcF cx)))%nat) by lia.
destruct (s19_refusal _ c _ i Hrc Hir) as [Hgs Hgl].
destruct (s19_kept _ m _ i Hmc Hi) as (Hws & Hwl & _).
destruct (s19_nkept_val _ m _ Hmc) as [_ H8].
destruct (s19_kept_nth _ _ i Mka Hir Hi) as [CK1 _].
destruct (s19_blocks cx ly S W regs mem md k acc c m HINV) as (Hc4 & Hcc & Hm4 & Hmc' & _).
pose proof HaC as (_ & _ & HmC & _). pose proof HaM as (_ & _ & HmM & _).
set (gs := nth i (SegModel.rc_refusal (x_rcF cx)) []) in *.
set (ws := fst (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))) in *.
unfold check_address_pre. unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
split; [lia|]. split; [exact Hgs|]. split; [lia|]. split; [exists c, 16616; split; [exact HinC | lia]|].
split; [apply (s19_sa_addr_sub _ c 16616); [exact HaC | lia | lia | lia]|].
split; [apply (s19_amem_sub c 16616); [exact HmC | lia | lia]|].
split; [lia|]. split; [exact Hws|]. split; [lia|]. split; [exists m, 9236; split; [exact HinM | lia]|].
split; [apply (s19_sa_addr_sub _ m 9236); [exact HaM | lia | lia | lia]|].
split; [apply (s19_amem_sub m 9236); [exact HmM | lia | lia]|].
exact CK1.
Qed.

(* check_knock_refused's pre at turn i: refusal[i] of c and kept_knock[i] of m (image A's twin s19_pre_ck,
   LLVMFuzzerTestOneInput_s19.v:816-839) *)
Lemma s19_pre_ck : forall cx ly S W regs mem md k acc c m i, s19_inv B MT cx ly S W regs mem md k acc c m ->
  (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  check_knock_refused_pre SEGS B ly S (rdW W mem) seg_litA_fz (c + 11912 + 200 * Z.of_nat i)
    (seg_spec.b2z (snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false)))) gotwA guardA
    (nth i (SegModel.rc_refusal (x_rcF cx)) []) (snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))).
Proof.
intros cx ly S W regs mem md k acc c m i HINV Hi.
pose proof HINV as ((_ & HIMG & _) & (HinC & _ & _ & HaC) & _ & _ & Hrc & Hmc).
change (sa_rconf (rdW W mem) c (x_rcF cx)) in Hrc. change (sa_mconf (rdW W mem) m (x_mcF cx)) in Hmc.
destruct (s19_model cx) as (_ & Mka & Mlen).
assert (Hir : (i < length (SegModel.rc_refusal (x_rcF cx)))%nat) by lia.
destruct (s19_refusal _ c _ i Hrc Hir) as [Hgs Hgl].
destruct (s19_nkept_val _ m _ Hmc) as [_ H8].
destruct (s19_kept_nth _ _ i Mka Hir Hi) as [_ CK2].
destruct (s19_blocks cx ly S W regs mem md k acc c m HINV) as (Hc4 & Hcc & _).
destruct HIMG as (_ & (_ & _ & HFZ & _ & _ & _ & _ & _ & HSSP & _) & _).
unfold check_knock_refused_pre. unfold seg_spec.SEG_C_SIZE in *.
split; [lia|]. split; [exact Hgs|]. split; [lia|]. split; [exists c, 16616; split; [exact HinC | lia]|].
split; [apply (s19_sa_addr_sub _ c 16616); [exact HaC | lia | lia | lia]|].
split; [reflexivity|]. split; [exact CK2|]. split; [|exact HSSP].
intros s0 Hs. apply (HFZ s0). unfold LTOI_FZ_LITS. apply in_or_app. right. apply in_or_app. left. exact Hs.
Qed.

(* ---- the loop's seed: the state at the head or a return point of the body (pc) is an instance of ss_L pc ---- *)
Lemma s19L_seed : forall cx ly S W regs mem md k acc c m i pc,
  lt_base B MT cx -> s19_inv B MT cx ly S W regs mem md k acc c m ->
  (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  lt_slots cx (rdW W mem) (s19_lslots c m) -> s19_lr regs c m i ->
  st_ok_pi SEGS VAL
    (s19L_E regs (Z.of_nat (length (SegModel.mc_kept (x_mcF cx))))
       (seg_spec.b2z (snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false)))) (m + 9100 + 4 * Z.of_nat i)) (ss_L pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 32 0) s19_SHL
    (s19L_E regs (Z.of_nat (length (SegModel.mc_kept (x_mcF cx))))
       (seg_spec.b2z (snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false)))) (m + 9100 + 4 * Z.of_nat i))
    (mrestrict (w_H W) mem).
Proof.
intros cx ly S W regs mem md k acc c m i pc HBASE HINV Hi LSL (R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof HINV as (HCORE & HBc & HBm & SLOTS & HCM).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & SAVED & HD0 & HD8 & HD16 & HFLW & S200 & FSH & S184) & _).
destruct (s19_frame_at B MT cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & STKc & S1c & SP47 & SP16 & S132 & SPtop).
assert (S1r : x_sp0 cx - 368 <= x_s1 cx <= x_sp0 cx - 352) by (destruct S1c as [Eq|Eq]; rewrite Eq; lia).
unfold STK_LLVMFuzzerTestOneInput in STKc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (s19_blocks cx ly S W regs mem md k acc c m HINV) as (Hc4 & Hcc & Hm4 & Hmc & Hcm & Hrc & Hac & Hrm & Ham).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
pose proof HCM as [HRC HMC].
change (seg_spec.seg_mc (x_run cx)) with (x_mcF cx) in HMC. change (seg_spec.seg_rc (x_run cx)) with (x_rcF cx) in HRC.
destruct (s19_nkept_val _ _ _ HMC) as (NKV & NK8).
destruct (s19_nref_val _ _ _ HRC) as (NRV & _).
destruct (s19_model cx) as (_ & _ & Mlen). rewrite Mlen in NRV.
destruct (s19_kept _ _ _ i HMC Hi) as (_ & _ & KNV).
set (nk := Z.of_nat (length (SegModel.mc_kept (x_mcF cx)))) in *.
set (kb := snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))) in *.
assert (Hkb : 0 <= seg_spec.b2z kb <= 1) by (destruct kb; cbn; lia).
assert (Hnk : 1 <= nk <= 8) by (unfold nk; lia).
set (E := s19L_E regs nk (seg_spec.b2z kb) (m + 9100 + 4 * Z.of_nat i)).
assert (EE : forall n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  ew E n = Z_to_bv 64 v /\ bv_unsigned (ew E n) = v).
{ intros n r v Hn Hr Hv. assert (En : ew E n = getr regs r) by (subst E; unfold s19L_E; apply ew_Eimg_Ereg_nat; exact Hn).
  rewrite En, Hr. split; [reflexivity|]. apply unsigned_lit_small. exact Hv. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (map (Z_to_bv 64) [SB; nk; seg_spec.b2z kb; m + 9100 + 4 * Z.of_nat i]) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold s19L_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth map] in E32, E33, E34, E35. clear EX.
destruct (EE 9%nat 9%bv (x_s1 cx) eq_refl Rs1 ltac:(lia)) as [E9 U9].
destruct (EE 18%nat 18%bv _ eq_refl R18 ltac:(lia)) as [E18 U18].
destruct (EE 21%nat 21%bv _ eq_refl R21 ltac:(lia)) as [E21 U21].
destruct (EE 22%nat 22%bv _ eq_refl R22 ltac:(lia)) as [E22 U22].
destruct (EE 23%nat 23%bv _ eq_refl R23 ltac:(lia)) as [E23 U23].
destruct (EE 24%nat 24%bv _ eq_refl R24 ltac:(lia)) as [E24 U24].
destruct (EE 25%nat 25%bv _ eq_refl R25 ltac:(lia)) as [E25 U25].
destruct (EE 26%nat 26%bv _ eq_refl R26 ltac:(lia)) as [E26 U26].
assert (U27 : bv_unsigned (ew E 27) = 2 ^ 64 + (112 * Z.of_nat i - 896)).
{ assert (En : ew E 27 = getr regs 27) by (subst E; unfold s19L_E; apply ew_Eimg_Ereg_nat; reflexivity).
  rewrite En, R27. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite <- (Z_mod_plus_full (112 * Z.of_nat i - 896) 1 (2 ^ 64)). rewrite Z.mod_small by lia. lia. }
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew E 33) = nk) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = seg_spec.b2z kb) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = m + 9100 + 4 * Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E32' : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact E32.
assert (RG : regs_ok E s19L_regs regs).
{ unfold s19L_regs. apply s19_regs_ok_set; [subst E; unfold s19L_E; apply regs_ok_Eimg_Ereg | reflexivity |].
  rewrite R19. symmetry. apply s19_denot_of_U. unfold s19_shx.
  rewrite (s19_U_sh E 22 32 (c + 13512) 0 E22 E32) by lia. rewrite Z.add_0_r. reflexivity. }
assert (SL : forall o v, In (o, v) (s19_lslots c m) -> rdword (rdW W mem) (x_s1 cx + o) = Some v) by exact LSL.
clearbody E.
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + exact RG.
  + vm_compute. reflexivity.
  + unfold ss_L, s19L_rf, s19L_rr, s19L_rn, s19L_rk. cbn [ss_mem].
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (s19_word_chunk W mem E _ (x_s1 cx) 128 (lt_not (m + 9100)));
           [apply SL; unfold s19_lslots; cbn [In]; repeat (first [left; reflexivity | right]) |].
         apply s19_denot_of_U. rewrite (s19_U_not E 26 (m + 9100) 0 E26) by lia. rewrite Z.add_0_r. reflexivity.
      -- apply (s19_word_chunk W mem E _ (x_s1 cx) 136 (lt_not (m + 8204)));
           [apply SL; unfold s19_lslots; cbn [In]; repeat (first [left; reflexivity | right]) |].
         apply s19_denot_of_U. rewrite (s19_U_not E 26 (m + 9100) (-896) E26) by lia. f_equal. lia.
      -- apply (s19_word_chunk W mem E _ (x_s1 cx) 144 (lt_not (c + 11912)));
           [apply SL; unfold s19_lslots; cbn [In]; repeat (first [left; reflexivity | right]) |].
         apply s19_denot_of_U. rewrite (s19_U_not E 18 (c + 11912) 0 E18) by lia. rewrite Z.add_0_r. reflexivity.
      -- apply (s19_word_chunk W mem E _ (x_s1 cx) 152 0);
           [apply SL; unfold s19_lslots; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity].
      -- apply (s19_word_chunk W mem E _ (x_s1 cx) 160 (shadow_addr (m + 9132)));
           [apply SL; unfold s19_lslots; cbn [In]; repeat (first [left; reflexivity | right]) |].
         apply s19_denot_of_U. unfold s19_shx. rewrite (s19_U_sh E 25 32 (m + 9132) 0 E25 E32) by lia.
         rewrite Z.add_0_r. reflexivity.
      -- apply (s19_word_chunk W mem E _ (x_s1 cx) 200 SHADOW_OFF S200).
         apply s19_denot_of_U. rewrite (U_atom E 32 SB E32) by (unfold SB; lia). reflexivity.
    * rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (s19_u32_chunk W mem E (SOff 33 0) (c + 13512) 0 nk); [rewrite Z.add_0_r; exact NRV | lia |].
      apply s19_denot_of_U. rewrite (U_atom E 33 nk E33) by lia. reflexivity.
    * rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (s19_u32_chunk W mem E (SOff 33 0) (m + 9132) 0 nk); [rewrite Z.add_0_r; exact NKV | lia |].
      apply s19_denot_of_U. rewrite (U_atom E 33 nk E33) by lia. reflexivity.
    * rewrite U35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (s19_u32_chunk W mem E (SOff 34 0) (m + 9100 + 4 * Z.of_nat i) 0 (seg_spec.b2z kb));
        [rewrite Z.add_0_r; exact KNV | lia |].
      apply s19_denot_of_U. rewrite (U_atom E 34 _ E34) by lia. reflexivity.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, ss_L, s19L_rf, s19L_rr, s19L_rn, s19L_rk.
    cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22, U25, U35.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [ss_L s19L_facts ss_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U18, U21, U22, U23, U24, U25, U26, U27, U32, U33, U34, U35.
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end. all: try exact I. all: try lia.
    * cbn [ss_L s19L_facts ss_facts f_alias alias_ok]. split; [|exact I].
      apply bv_eq. change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 26 0) (SOff 21 0))))
        with (U E (SAlu ALU_ADD (SOff 26 0) (SOff 21 0))).
      change (bv_unsigned (sv_denot E (SOff 35 0))) with (U E (SOff 35 0)).
      rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 26 _ E26), (U_atom E 21 _ E21), (U_atom E 35 _ E35) by lia.
      apply zcanon_id. unfold M64. lia.
- unfold sh_ok, s19_SHL. repeat apply Forall_cons; try apply Forall_nil.
  + apply (s19_shent W mem E 22 c 16616 (c + 13512) 0 8 Hrc Hac E32' E22); lia.
  + apply (s19_shent W mem E 25 m 9236 (m + 9132) 0 8 Hrm Ham E32' E25); lia.
  + apply (s19_shent W mem E 35 m 9236 (m + 9100 + 4 * Z.of_nat i) 0 8 Hrm Ham E32' E35); lia.
Qed.
Ltac s19_awr_ro :=
  unfold awr_ok; intros ?a (?r & ?Hin & ?Hr); exfalso; vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin.

(* the body's two return points: after check_address (0x857e4) and after check_knock_refused (0x85814) *)
Definition s19_PA (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc c m,
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  s19_inv B MT cx ly S W regs mem md k acc c m -> lt_slots cx (rdW W mem) (s19_lslots c m) ->
  s19_lr regs c m i -> getr regs 20 = w64 (c + 11912 + 200 * Z.of_nat i) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_CA_RA)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Definition s19_PK (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc c m,
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  s19_inv B MT cx ly S W regs mem md k acc c m -> lt_slots cx (rdW W mem) (s19_lslots c m) ->
  s19_lr regs c m i -> getr regs 20 = w64 (c + 11912 + 200 * Z.of_nat i) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_CK_RA)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* ---- 0x857a8 .. 0x857e0: 152(s1) = C & 7 = 0 (trap 0x857ac), check 21 (n_refusals' shadow), i < n_refusals,
   the two pointer-overflow traps 0x857c4 / 0x857d0, a0 = refusal[i], a1 = kept[i], jal check_address ---- *)
Lemma s19_stepH : forall i, s19_PA i -> K857a8_stmt B MT i.
Proof.
intros i HPA. unfold K857a8_stmt.
intros cx ly S W regs mem md k acc c m HBASE HFRM Hi HINV LSL R18 R19 R21 R22 R23 R24 R25 R26 R27.
assert (HLR : s19_lr regs c m i) by (repeat split; assumption).
destruct (s19L_seed cx ly S W regs mem md k acc c m i LO_K857a8 HBASE HINV Hi LSL HLR) as [HS SHOK].
pose proof HINV as (HCORE & HBc & HBm & SLOTS & HCM).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & _) & _ & _ & HBUD).
destruct (s19_frame_at B MT cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & STKc & S1c & SP47 & SP16 & S132 & SPtop).
assert (S1r : x_sp0 cx - 368 <= x_s1 cx <= x_sp0 cx - 352) by (destruct S1c as [Eq|Eq]; rewrite Eq; lia).
unfold STK_LLVMFuzzerTestOneInput in STKc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (s19_blocks cx ly S W regs mem md k acc c m HINV) as (Hc4 & Hcc & Hm4 & Hmc & Hcm & _).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
pose proof HCM as [HRC HMC].
change (seg_spec.seg_mc (x_run cx)) with (x_mcF cx) in HMC. change (seg_spec.seg_rc (x_run cx)) with (x_rcF cx) in HRC.
destruct (s19_nkept_val _ _ _ HMC) as (NKV & NK8).
set (nk := Z.of_nat (length (SegModel.mc_kept (x_mcF cx)))) in *.
set (kb := snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))) in *.
set (E := s19L_E regs nk (seg_spec.b2z kb) (m + 9100 + 4 * Z.of_nat i)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s19L_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold s19L_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (map (Z_to_bv 64) [SB; nk; seg_spec.b2z kb; m + 9100 + 4 * Z.of_nat i]) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold s19L_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth map] in E32, E33. clear EX.
assert (U27s : forall o, 896 <= o <= 1008 -> U E (SOff 27 o) = 112 * Z.of_nat i - 896 + o).
{ intros o Ho. rewrite U_SOff, (EE 27%nat 27%bv eq_refl), R27. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). unfold zcanon, M64. rewrite Zplus_mod_idemp_l. apply Z.mod_small. lia. }
clearbody E.
paj_run_tok RUN HS HJ SHOK s19_span.
{ s19_awr_ro. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
pose proof (frame_of_read_only E (ss_mem (ss_L LO_K857a8)) mem (ms_mem ms) eq_refl HF) as Hmem.
clear HF HFr HG.
assert (D24 : sv_denot E (SOff 24 0) = Z_to_bv 64 (Z.of_nat i)).
{ rewrite (s19_denot_off E 24 (Z.of_nat i) 0) by (first [rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia]).
  rewrite Z.add_0_r. reflexivity. }
assert (D33 : sv_denot E (SOff 33 0) = Z_to_bv 64 nk).
{ rewrite (s19_denot_off E 33 nk 0 E33) by (unfold nk; lia). rewrite Z.add_0_r. reflexivity. }
psrr_branch_tok RUN BR HS SHOK s19_span.
- (* i >= n_refusals: refuted, n_refusals = n_kept > i *)
  exfalso. rewrite (s19_br_ge E _ _ (Z.of_nat i) nk D24 D33) in Hc by (unfold nk; lia).
  apply negb_true_iff, Z.ltb_ge in Hc. unfold nk in Hc. lia.
- clear Hc.
  paj_run_tok RUN HS HJ SHOK s19_span.
  { s19_awr_ro. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdvx := d) in *; clearbody mdvx end.
  psrr_branch_tok RUN BR HS SHOK s19_span.
  { (* trap 0x857c4: ~(C + 0x2e88) <u 200 i, refuted *)
    exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
    rewrite (YI08.U_not E 18 (c + 11912)) in Hc by (first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | lia]).
    rewrite (U_atom E 23 (200 * Z.of_nat i)) in Hc by (first [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia]).
    lia. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK s19_span.
  { s19_awr_ro. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdvy := d) in *; clearbody mdvy end.
  psrr_branch_tok RUN BR HS SHOK s19_span.
  { (* trap 0x857d0: ~(M + 0x200c) <u 112 i, refuted *)
    exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
    rewrite (YI08.U_not_off E 26 (m + 9100) (-896)) in Hc
      by (first [rewrite (EE 26%nat 26%bv eq_refl); exact R26 | lia]).
    rewrite (U27s 896) in Hc by lia. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK s19_span.
  { s19_awr_ro. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  assert (Hm2 : ms_mem ms2 = mem).
  { rewrite <- Hmem.
    pose proof (fun H => frame_of_read_only E _ _ _ H HF) as X0. specialize (X0 ltac:(vm_compute; reflexivity)).
    pose proof (fun H => frame_of_read_only E _ _ _ H HF0) as X1. specialize (X1 ltac:(vm_compute; reflexivity)).
    pose proof (fun H => frame_of_read_only E _ _ _ H HF1) as X2. specialize (X2 ltac:(vm_compute; reflexivity)).
    rewrite X2, X1, X0. reflexivity. }
  clear HF HFr HG HF0 HFr0 HG0 HF1 HFr1 HG1.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  s19_rreg HS (10%bv : bv 5) P10. s19_rreg HS (11%bv : bv 5) P11. s19_rreg HS (20%bv : bv 5) P20.
  s19_rreg HS (18%bv : bv 5) P18. s19_rreg HS (19%bv : bv 5) P19. s19_rreg HS (21%bv : bv 5) P21.
  s19_rreg HS (22%bv : bv 5) P22. s19_rreg HS (23%bv : bv 5) P23. s19_rreg HS (24%bv : bv 5) P24.
  s19_rreg HS (25%bv : bv 5) P25. s19_rreg HS (26%bv : bv 5) P26. s19_rreg HS (27%bv : bv 5) P27.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  pmkst HS.
  rewrite Hm2 in HJ |- *.
  rewrite (SIGP SS_check_address ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_check_address) with AF_check_address by (vm_compute; reflexivity).
  assert (DO : forall n, sv_denot E (SOff n 0) = ew E n)
    by (intros n; cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (E18 : ew E 18 = Z_to_bv 64 (c + 11912)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
  assert (E22 : ew E 22 = Z_to_bv 64 (c + 13512)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (E23 : ew E 23 = Z_to_bv 64 (200 * Z.of_nat i)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
  assert (E26 : ew E 26 = Z_to_bv 64 (m + 9100)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (HLR1 : s19_lr (ms_regs ms2) c m i).
  { unfold s19_lr. rewrite P18, P19, P21, P22, P23, P24, P25, P26, P27, !DO.
    rewrite (EE 18%nat 18%bv eq_refl), (EE 21%nat 21%bv eq_refl), (EE 22%nat 22%bv eq_refl),
      (EE 23%nat 23%bv eq_refl), (EE 24%nat 24%bv eq_refl), (EE 25%nat 25%bv eq_refl), (EE 26%nat 26%bv eq_refl),
      (EE 27%nat 27%bv eq_refl).
    split; [exact R18|]. split.
    { apply s19_denot_of_U. unfold w64. rewrite (s19_U_sh E 22 32 (c + 13512) 0 E22 E32) by lia.
      rewrite Z.add_0_r. reflexivity. }
    repeat split; assumption. }
  assert (U10 : U E (SAlu ALU_ADD (SOff 18 0) (SOff 23 0)) = c + 11912 + 200 * Z.of_nat i).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 18 _ E18), (U_atom E 23 _ E23) by lia.
    apply zcanon_id. unfold M64. lia. }
  assert (U11 : U E (SAlu ALU_ADD (SOff 26 0) (SOff 27 0)) = m + 8204 + 112 * Z.of_nat i).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 26 _ E26) by lia.
    rewrite U_SOff, (EE 27%nat 27%bv eq_refl), R27. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). unfold zcanon, M64. rewrite Z.add_0_r, Zmod_mod, Zplus_mod_idemp_r.
    replace (m + 9100 + (112 * Z.of_nat i - 896)) with (m + 8204 + 112 * Z.of_nat i) by lia.
    apply Z.mod_small. lia. }
  pose proof (s19_reg_U _ _ _ _ _ P10 U10) as Q10. pose proof (s19_reg_U _ _ _ _ _ P11 U11) as Q11.
  pose proof (s19_reg_U _ _ _ _ _ P20 U10) as Q20.
  assert (HINV1 : s19_inv B MT cx ly S W (ms_regs ms2) mem mdv2 k acc c m).
  { apply (s19_inv_xfer B MT cx ly S W regs mem md k acc c m ly S W (ms_regs ms2) mem mdv2 HBASE HINV HJ
      P2 P3 P4 P8 P9).
    - intros a Ha _. reflexivity.
    - apply Permutation_refl.
    - exact (proj1 (proj2 (proj2 (proj2 HBUD)))). }
  pose proof (s19_inv_nev B MT cx ly S W _ _ mdv2 k acc c m HBASE HINV1) as HNEV.
  pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
  apply (s19_prog_call B MT MTFL STK_check_address (BASE + AF_check_address) cx ly S W (ms_regs ms2) mem mdv2
    k acc c m (getr (ms_regs ms2) 1) HBASE HINV1 ltac:(unfold STK_check_address, YG0d.ESTACK; lia) eq_refl).
  + rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  + rewrite P1. rewrite unsigned_lit_small; lia.
  + intros ch HPRE1. pose proof HINV1 as ((_ & (HARO & _) & _) & _).
    exact (HCA fx ly S W (ms_regs ms2) mem mdv2 ch _ _ _ _ HPRE1 HARO Q10 ltac:(lia) Q11 ltac:(lia)
      (s19_pre_ca cx ly S W _ mem mdv2 k acc c m i HINV1 Hi) ltac:(unfold EV_check_address; lia)).
  + intros W2 ly2 S2 regs2 mem2 md2 HINV2 HP2 KK2. rewrite P1.
    apply (HPA cx ly2 S2 W2 regs2 mem2 md2 k acc c m HBASE HFRM Hi HINV2).
    * apply (s19_slots_xfer cx (rdW W mem)); [|exact LSL].
      intros o v Hin q Hq. unfold s19_lslots in Hin. cbn [In] in Hin.
      apply KK2; [|right]; repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <-; lia|]); destruct Hin.
    * exact (s19_lr_pres _ _ c m i HP2 HLR1).
    * rewrite (s19_pres (ms_regs ms2) regs2 20 HP2) by s19_cs. exact Q20.
Qed.

(* ---- 0x857e4 .. 0x85810: the shadow base, trap 0x857e8 (s11 = 112 i - 896 <> 0), trap 0x857f0, check 22
   (kept_knock[i]'s shadow), a1 = kept_knock[i], a0 = refusal[i], jal check_knock_refused ---- *)
Lemma s19_stepCA : forall i, s19_PK i -> s19_PA i.
Proof.
intros i HPK. unfold s19_PA.
intros cx ly S W regs mem md k acc c m HBASE HFRM Hi HINV LSL HLR R20.
destruct (s19L_seed cx ly S W regs mem md k acc c m i LO_CA_RA HBASE HINV Hi LSL HLR) as [HS SHOK].
pose proof HINV as (HCORE & HBc & HBm & SLOTS & HCM).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & _) & _ & _ & HBUD).
destruct (s19_frame_at B MT cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & STKc & S1c & SP47 & SP16 & S132 & SPtop).
assert (S1r : x_sp0 cx - 368 <= x_s1 cx <= x_sp0 cx - 352) by (destruct S1c as [Eq|Eq]; rewrite Eq; lia).
unfold STK_LLVMFuzzerTestOneInput in STKc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (s19_blocks cx ly S W regs mem md k acc c m HINV) as (Hc4 & Hcc & Hm4 & Hmc & Hcm & _).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
pose proof HCM as [HRC HMC].
change (seg_spec.seg_mc (x_run cx)) with (x_mcF cx) in HMC. change (seg_spec.seg_rc (x_run cx)) with (x_rcF cx) in HRC.
destruct (s19_nkept_val _ _ _ HMC) as (NKV & NK8).
pose proof HLR as (R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
set (nk := Z.of_nat (length (SegModel.mc_kept (x_mcF cx)))) in *.
set (kb := snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))) in *.
set (E := s19L_E regs nk (seg_spec.b2z kb) (m + 9100 + 4 * Z.of_nat i)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s19L_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold s19L_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (map (Z_to_bv 64) [SB; nk; seg_spec.b2z kb; m + 9100 + 4 * Z.of_nat i]) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold s19L_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth map] in E32, E33, E34, E35. clear EX.
assert (U27s : forall o, 0 <= o <= 1008 -> U E (SOff 27 o) = (2 ^ 64 + (112 * Z.of_nat i - 896) + o) mod 2 ^ 64).
{ intros o Ho. rewrite U_SOff, (EE 27%nat 27%bv eq_refl), R27. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). unfold zcanon, M64. rewrite Zplus_mod_idemp_l.
  rewrite <- (Z_mod_plus_full (112 * Z.of_nat i - 896 + o) 1 (2 ^ 64)). f_equal. lia. }
assert (DO : forall n, sv_denot E (SOff n 0) = ew E n)
  by (intros n; cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
clearbody E.
paj_run_tok RUN HS HJ SHOK s19_span.
{ s19_awr_ro. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
pose proof (frame_of_read_only E (ss_mem (ss_L LO_CA_RA)) mem (ms_mem ms) eq_refl HF) as Hmem.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK s19_span.
{ (* trap 0x857f0: ~(M + 0x238c) <u 4 i, refuted *)
  exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  rewrite (YI08.U_not E 26 (m + 9100)) in Hc by (first [rewrite (EE 26%nat 26%bv eq_refl); exact R26 | lia]).
  rewrite (U_atom E 21 (4 * Z.of_nat i)) in Hc by (first [rewrite (EE 21%nat 21%bv eq_refl); exact R21 | lia]).
  lia. }
clear Hc.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdvx := d) in *; clearbody mdvx end.
paj_run_tok RUN HS HJ SHOK s19_span.
{ s19_awr_ro. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?x; cfg_model := _ |} _ => rename x into msF end.
  assert (Hm2 : ms_mem msF = mem).
  { rewrite <- Hmem.
    repeat match goal with HFx : frame_of E _ _ _ |- _ =>
      let X := fresh "X" in pose proof (fun H => frame_of_read_only E _ _ _ H HFx) as X;
      specialize (X ltac:(vm_compute; reflexivity)); rewrite X; clear HFx end.
    reflexivity. }
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
s19_rreg HS (10%bv : bv 5) P10. s19_rreg HS (11%bv : bv 5) P11. s19_rreg HS (20%bv : bv 5) P20.
s19_rreg HS (18%bv : bv 5) P18. s19_rreg HS (19%bv : bv 5) P19. s19_rreg HS (21%bv : bv 5) P21.
s19_rreg HS (22%bv : bv 5) P22. s19_rreg HS (23%bv : bv 5) P23. s19_rreg HS (24%bv : bv 5) P24.
s19_rreg HS (25%bv : bv 5) P25. s19_rreg HS (26%bv : bv 5) P26. s19_rreg HS (27%bv : bv 5) P27.
rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
pmkst HS.
rewrite Hm2 in HJ |- *.
rewrite (SIGP SS_check_knock_refused ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_knock_refused) with AF_check_knock_refused by (vm_compute; reflexivity).
assert (E22 : ew E 22 = Z_to_bv 64 (c + 13512)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (HLR1 : s19_lr (ms_regs msF) c m i).
{ unfold s19_lr. rewrite P18, P19, P21, P22, P23, P24, P25, P26, P27, !DO.
  rewrite (EE 18%nat 18%bv eq_refl), (EE 21%nat 21%bv eq_refl), (EE 22%nat 22%bv eq_refl),
    (EE 23%nat 23%bv eq_refl), (EE 24%nat 24%bv eq_refl), (EE 25%nat 25%bv eq_refl), (EE 26%nat 26%bv eq_refl),
    (EE 27%nat 27%bv eq_refl).
  split; [exact R18|]. split.
  { apply s19_denot_of_U. unfold w64. rewrite (s19_U_sh E 22 32 (c + 13512) 0 E22 E32) by lia.
    rewrite Z.add_0_r. reflexivity. }
  repeat split; assumption. }
assert (Q20 : getr (ms_regs msF) 20 = w64 (c + 11912 + 200 * Z.of_nat i))
  by (rewrite P20, DO, (EE 20%nat 20%bv eq_refl); exact R20).
assert (Q10 : getr (ms_regs msF) 10 = w64 (c + 11912 + 200 * Z.of_nat i))
  by (rewrite P10, DO, (EE 20%nat 20%bv eq_refl); exact R20).
assert (Q11 : getr (ms_regs msF) 11 = w64 (seg_spec.b2z kb)) by (rewrite P11, DO, E34; reflexivity).
assert (HINV1 : s19_inv B MT cx ly S W (ms_regs msF) mem mdv2 k acc c m).
{ apply (s19_inv_xfer B MT cx ly S W regs mem md k acc c m ly S W (ms_regs msF) mem mdv2 HBASE HINV HJ
    P2 P3 P4 P8 P9).
  - intros a Ha _. reflexivity.
  - apply Permutation_refl.
  - exact (proj1 (proj2 (proj2 (proj2 HBUD)))). }
pose proof (s19_inv_nev B MT cx ly S W _ _ mdv2 k acc c m HBASE HINV1) as HNEV.
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
assert (Hkb : 0 <= seg_spec.b2z kb < 2 ^ 64) by (destruct kb; cbn; lia).
apply (s19_prog_call B MT MTFL STK_check_knock_refused (BASE + AF_check_knock_refused) cx ly S W (ms_regs msF) mem
  mdv2 k acc c m (getr (ms_regs msF) 1) HBASE HINV1 ltac:(unfold STK_check_knock_refused, YG0d.ESTACK; lia) eq_refl).
- rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite P1. rewrite unsigned_lit_small; lia.
- intros ch HPRE1. pose proof HINV1 as ((_ & (HARO & _) & _) & _).
  exact (HCK fx ly S W (ms_regs msF) mem mdv2 ch _ _ _ _ HPRE1 HARO Q10 ltac:(lia) Q11 Hkb
    (s19_pre_ck cx ly S W _ mem mdv2 k acc c m i HINV1 Hi) ltac:(unfold EV_check_knock_refused; lia)).
- intros W2 ly2 S2 regs2 mem2 md2 HINV2 HP2 KK2. rewrite P1.
  apply (HPK cx ly2 S2 W2 regs2 mem2 md2 k acc c m HBASE HFRM Hi HINV2).
  + apply (s19_slots_xfer cx (rdW W mem)); [|exact LSL].
    intros o v Hin q Hq. unfold s19_lslots in Hin. cbn [In] in Hin.
    apply KK2; [|right]; repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <-; lia|]); destruct Hin.
  + exact (s19_lr_pres _ _ c m i HP2 HLR1).
  + rewrite (s19_pres (ms_regs msF) regs2 20 HP2) by s19_cs. exact Q20.
Qed.

(* ---- 0x85814 .. 0x85838: check 23 (n_kept's shadow), n_kept, i += 1 and the steps, blt i, n_kept: to the head of
   turn i + 1 or out to K85868 ---- *)
Lemma s19_stepCK : LTA_K85868 B MT -> forall i, K857a8_stmt B MT (Datatypes.S i) -> s19_PK i.
Proof.
intros HX i HIH. unfold s19_PK.
intros cx ly S W regs mem md k acc c m HBASE HFRM Hi HINV LSL HLR R20.
destruct (s19L_seed cx ly S W regs mem md k acc c m i LO_CK_RA HBASE HINV Hi LSL HLR) as [HS SHOK].
pose proof HINV as (HCORE & HBc & HBm & SLOTS & HCM).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & _) & _ & _ & HBUD).
destruct (s19_frame_at B MT cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & STKc & S1c & SP47 & SP16 & S132 & SPtop).
assert (S1r : x_sp0 cx - 368 <= x_s1 cx <= x_sp0 cx - 352) by (destruct S1c as [Eq|Eq]; rewrite Eq; lia).
unfold STK_LLVMFuzzerTestOneInput in STKc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (s19_blocks cx ly S W regs mem md k acc c m HINV) as (Hc4 & Hcc & Hm4 & Hmc & Hcm & _).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
pose proof HCM as [HRC HMC].
change (seg_spec.seg_mc (x_run cx)) with (x_mcF cx) in HMC. change (seg_spec.seg_rc (x_run cx)) with (x_rcF cx) in HRC.
destruct (s19_nkept_val _ _ _ HMC) as (NKV & NK8).
pose proof HLR as (R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
set (nk := Z.of_nat (length (SegModel.mc_kept (x_mcF cx)))) in *.
set (kb := snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))) in *.
set (E := s19L_E regs nk (seg_spec.b2z kb) (m + 9100 + 4 * Z.of_nat i)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s19L_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold s19L_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (map (Z_to_bv 64) [SB; nk; seg_spec.b2z kb; m + 9100 + 4 * Z.of_nat i]) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold s19L_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth map] in E32, E33, E34, E35. clear EX.
assert (U27s : forall o, 0 <= o <= 1008 -> U E (SOff 27 o) = (2 ^ 64 + (112 * Z.of_nat i - 896) + o) mod 2 ^ 64).
{ intros o Ho. rewrite U_SOff, (EE 27%nat 27%bv eq_refl), R27. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). unfold zcanon, M64. rewrite Zplus_mod_idemp_l.
  rewrite <- (Z_mod_plus_full (112 * Z.of_nat i - 896 + o) 1 (2 ^ 64)). f_equal. lia. }
assert (DO : forall n, sv_denot E (SOff n 0) = ew E n)
  by (intros n; cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
clearbody E.
paj_run_tok RUN HS HJ SHOK s19_span.
{ s19_awr_ro. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
pose proof (frame_of_read_only E (ss_mem (ss_L LO_CK_RA)) mem (ms_mem ms) eq_refl HF) as Hmem.
clear HF HFr HG.
assert (E24 : ew E 24 = w64 (Z.of_nat i)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (D24 : sv_denot E (SOff 24 1) = Z_to_bv 64 (Z.of_nat i + 1)) by exact (s19_denot_off_w E 24 _ 1 E24).
assert (D33 : sv_denot E (SOff 33 0) = Z_to_bv 64 nk).
{ rewrite (s19_denot_off E 33 nk 0 E33) by (unfold nk; lia). rewrite Z.add_0_r. reflexivity. }
psrr_branch_tok RUN BR HS SHOK s19_span.
- (* i + 1 < n_kept: the head of turn i + 1 *)
  assert (Hlt : (Datatypes.S i < length (SegModel.mc_kept (x_mcF cx)))%nat).
  { rewrite (s19_br_lt E _ _ (Z.of_nat i + 1) nk D24 D33) in Hc by (unfold nk; lia).
    apply Z.ltb_lt in Hc. unfold nk in Hc. lia. }
  clear Hc.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdvx := d) in *; clearbody mdvx end.
  paj_run_to_tok RUNTO HS HJ SHOK s19_span LO_K857a8.
  { s19_awr_ro. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?x; cfg_model := _ |} _ => rename x into msF end.
  assert (Hm2 : ms_mem msF = mem).
  { rewrite <- Hmem.
    repeat match goal with HFx : frame_of E _ _ _ |- _ =>
      let X := fresh "X" in pose proof (fun H => frame_of_read_only E _ _ _ H HFx) as X;
      specialize (X ltac:(vm_compute; reflexivity)); rewrite X; clear HFx end.
    reflexivity. }
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  s19_rreg HS (18%bv : bv 5) P18. s19_rreg HS (19%bv : bv 5) P19. s19_rreg HS (21%bv : bv 5) P21.
  s19_rreg HS (22%bv : bv 5) P22. s19_rreg HS (23%bv : bv 5) P23. s19_rreg HS (24%bv : bv 5) P24.
  s19_rreg HS (25%bv : bv 5) P25. s19_rreg HS (26%bv : bv 5) P26. s19_rreg HS (27%bv : bv 5) P27.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ _ _; cfg_model := _ |} _ => set (regsF := rg) in * end.
  rewrite Hm2 in HJ |- *.
  assert (HINV1 : s19_inv B MT cx ly S W regsF mem mdv2 k acc c m).
  { apply (s19_inv_xfer B MT cx ly S W regs mem md k acc c m ly S W regsF mem mdv2 HBASE HINV HJ
      P2 P3 P4 P8 P9).
    - intros a Ha _. reflexivity.
    - apply Permutation_refl.
    - exact (proj1 (proj2 (proj2 (proj2 HBUD)))). }
  assert (E22 : ew E 22 = Z_to_bv 64 (c + 13512)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (EW : forall n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v -> ew E n = w64 v)
    by (intros n r v Hn Hr; rewrite (EE n r Hn); exact Hr).
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?p)) _ _; cfg_model := _ |} _ =>
    let v := eval vm_compute in p in replace p with v by (vm_compute; reflexivity) end.
  apply (HIH cx ly S W regsF mem mdv2 k acc c m HBASE HFRM Hlt HINV1 LSL).
  + rewrite P18, DO, (EE 18%nat 18%bv eq_refl). exact R18.
  + rewrite P19. apply s19_denot_of_U. unfold w64. rewrite (s19_U_sh E 22 32 (c + 13512) 0 E22 E32) by lia.
    rewrite Z.add_0_r. reflexivity.
  + rewrite P21, (s19_denot_off_w E 21 _ 4 (EW 21%nat 21%bv _ eq_refl R21)). f_equal. lia.
  + rewrite P22, DO, (EE 22%nat 22%bv eq_refl). exact R22.
  + rewrite P23, (s19_denot_off_w E 23 _ 200 (EW 23%nat 23%bv _ eq_refl R23)). f_equal. lia.
  + rewrite P24, (s19_denot_off_w E 24 _ 1 E24). f_equal. lia.
  + rewrite P25, DO, (EE 25%nat 25%bv eq_refl). exact R25.
  + rewrite P26, DO, (EE 26%nat 26%bv eq_refl). exact R26.
  + rewrite P27, (s19_denot_off_w E 27 _ 112 (EW 27%nat 27%bv _ eq_refl R27)). f_equal. lia.
- (* i + 1 = n_kept: out to K85868 *)
  clear Hc.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdvx := d) in *; clearbody mdvx end.
  paj_run_to_tok RUNTO HS HJ SHOK s19_span LO_K85868.
  { s19_awr_ro. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?x; cfg_model := _ |} _ => rename x into msF end.
  assert (Hm2 : ms_mem msF = mem).
  { rewrite <- Hmem.
    repeat match goal with HFx : frame_of E _ _ _ |- _ =>
      let X := fresh "X" in pose proof (fun H => frame_of_read_only E _ _ _ H HFx) as X;
      specialize (X ltac:(vm_compute; reflexivity)); rewrite X; clear HFx end.
    reflexivity. }
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  pmkst HS.
  rewrite Hm2 in HJ |- *.
  assert (HINV1 : s19_inv B MT cx ly S W (ms_regs msF) mem mdv2 k acc c m).
  { apply (s19_inv_xfer B MT cx ly S W regs mem md k acc c m ly S W (ms_regs msF) mem mdv2 HBASE HINV HJ
      P2 P3 P4 P8 P9).
    - intros a Ha _. reflexivity.
    - apply Permutation_refl.
    - exact (proj1 (proj2 (proj2 (proj2 HBUD)))). }
  destruct HINV1 as (HC2 & HBc2 & HBm2 & SL2 & HCM2).
  exact (HX fx cx ly S W (ms_regs msF) mem mdv2 k acc c m HBASE HFRM HC2 HBc2 HBm2 SL2 HCM2).
Qed.

(* no turn i >= 8 is reached: n_kept <= 8 *)
Lemma s19_K857a8_vac : forall i, (8 <= i)%nat -> K857a8_stmt B MT i.
Proof.
intros i Hi. unfold K857a8_stmt. intros cx ly S W regs mem md k acc c m _ _ Hn (_ & _ & _ & _ & (_ & Hmc)). exfalso.
change (sa_mconf (rdW W mem) m (x_mcF cx)) in Hmc.
destruct (s19_nkept_val _ m _ Hmc) as [_ H8]. lia.
Qed.

(* the loop, turn by turn from the last *)
Lemma s19_loop : LTA_K85868 B MT -> forall j i, (i + j = 8)%nat -> K857a8_stmt B MT i.
Proof.
intros HX j. induction j as [|j IH]; intros i Hij.
- apply s19_K857a8_vac. lia.
- apply s19_stepH, s19_stepCA, (s19_stepCK HX). apply IH. lia.
Qed.

(* ---- the segment ---- *)
Theorem lt_seg_S10 : lt_seg_S10_stmt B MT.
Proof.
unfold lt_seg_S10_stmt. intros HX.
exact (s19_head HX (s19_loop HX 8 0 eq_refl)).
Qed.
End e.
End f.
End d.
