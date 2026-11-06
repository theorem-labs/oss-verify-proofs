(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its module names and numbers changed; 721 of its 814 lines of code are new or changed and 393 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), kinds 0 and 7 after the head: from the
   private cut at +0x960 (kernel_k07h_b.v k7_c960) to the attribute loop's head (kin_attr, +0x9d8) or to nl_end
   (kin_nlend, +0x106c). Listing (internal path) (internal record, sha256 7bc02d6772b3), +0x960
   .. +0x9d4, +0x1b9c .. +0x1ba4:
     +0x960  lbu a0, 0(s8); beqz; errpath          the instrumented check of the cursor's n word
     +0x96c  ld a0, 0(s3); beqz a0 -> +0x106c       n = 0: no attribute
     +0x974  lbu a1, 0(s8); beqz; errpath; a0 := n - 1; sd a0, 8(s2)
     +0x988  ld a0, 0xc0(s1); lbu a0, 0(a0)         the check of the cursor's p word (slot 0xc0 = shadow(a0))
     +0x998  a0 := p; [a0] := p + 1
     +0x9a4  lb a1, shadow(p); beqz -> +0x9b8; j +0x1b9c: andi a2, a0, 7; bge a2, a1 -> errpath; j +0x9b8
     +0x9b8  lbu a0, 0(a0)                          the input byte b
     +0x9bc  a1 := [0x10310] (0x3333333333333334); s6 := b - mulhu(b, M) - 4 mulhu(b, M) = b % 5
     +0x9d4  beqz s6 -> +0x106c                     else +0x9d8 with s6 = b % 5 in 1..4
   TWO PHASES with a private cut at +0x9bc (k7_c9bc: the byte b in a0, the cursor at adv + 1), so that the .rodata
   word at 0x10310 and the input byte are never regions of one state (the input may lie anywhere in the read set):
   (A1) k7a_p1: +0x960 -> +0x9bc / +0x106c. n = 0 (k7a_zero): one run, no memory written. n >= 1: the input byte b at
   p and its shadow byte s (at the current memory: kernel_kit.v kn_input_at) are atoms; the proof cases on s = 0 or
   s in [1, 7] (an atom with the condition p & 7 < s, saddr_ok); each run ends at +0x9bc; the cut there is k7_land
   (kernel_kit.v's part lemmas with the change set = the cursor; the cursor restated at adv + 1). The model of the
   state is kernel_msg0_c.v's (the message count).
   (A2) k7m_p: +0x9bc -> +0x9d8 / +0x106c: the multiplier's region (kernel_img.v ki_m5_val_mem, KI) and a condition on
   the engine's own expression of s6 (k7_m5, whose value is b % 5 by k7_m5_val, a table over the 256 bytes); no memory
   written.
   Section hypotheses used: LAWS (the run instances), TB (the read set's shadow at the current memory), LV (the
   .rodata word's address), KI (its value).
   Released proofs (rule 24): none of kernel's walk (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by
   the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PcapRelro kernel_defs kernel_kit kernel_next kernel_msg0_kit kernel_k3 kernel_k07h_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition KP_K9BC : Z := 0x9bc.   (* kinds 0, 7: `auipc a1`, the multiplier's load, after the input byte *)

(* ---- (A1) the symbolic states at +0x960 ---- *)
(* n = 0: the cursor's n word the literal 0 *)
Definition k7z_cur : YP09.region := YP09.mkRegion (Some 18%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SLit 0))].
Definition k7z_ss : sstate := mkSS (kpc KP_K960) km_regsA [k7z_cur] None (mkFacts km_atoms [] []).

(* n >= 1: atoms 32 = p, 33 = n, 34 = shadow(p), 35 = s (the shadow byte of p), 36 = b (the input byte at p) *)
Definition k7a_cur : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition k7a_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0 0 [YP09.mkChunk 0xc0 (CVal 8 (km_sh 18 0))].
Definition k7a_in : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition k7a_shr (fast : bool) : YP09.region :=
  YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (if fast then SLit 0 else SOff 35 0))].
Definition k7a_facts (fast : bool) : facts :=
  mkFacts (km_atoms ++ [(33%nat, mkAF 1 (2 ^ 64 - 1) 0); (36%nat, mkAF 0 255 0)] ++
           (if fast then [] else [(35%nat, mkAF 1 7 0)]))
    (if fast then [] else [mkAC BC_LT (SAlu ALU_AND (SOff 32 0) (SLit 7)) (SOff 35 0)])
    [(km_sh 32 0, SOff 34 0)].
Definition k7a_ss (fast : bool) : sstate :=
  mkSS (kpc KP_K960) km_regsA [k7a_cur; k7a_sl; k7a_in; k7a_shr fast] None (k7a_facts fast).

(* ---- (A2) the symbolic state at +0x9bc: a0 = b; the multiplier's word ---- *)
Definition k7_m5 : sv :=
  SAlu ALU_SUB
    (SAlu ALU_SUB (SOff 10 0) (SMd M_MULHU (SOff 10 0) (SLit 3689348814741910324)))
    (SAlu ALU_SLL (SMd M_MULHU (SOff 10 0) (SLit 3689348814741910324)) (SLit 2)).
Definition k7m_rg : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 17)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit KI_M5_V))].
Definition k7m_ss (zero : bool) : sstate :=
  mkSS (kpc KP_K9BC) sr_atoms [k7m_rg] None (mkFacts [] [mkAC (if zero then BC_EQ else BC_NE) k7_m5 (SLit 0)] []).

(* the engine's s6 is b % 5 *)
Lemma k7_m5_val : forall (E : env) b, ew E 10%nat = Z_to_bv 64 b -> 0 <= b < 256 ->
  sv_denot E k7_m5 = Z_to_bv 64 (b mod 5).
Proof.
  intros E b Hb Hr. unfold k7_m5. cbn [sv_denot]. rewrite !Hb.
  assert (Hin : In b (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat b). split; [apply Z2Nat.id; lia | apply in_seq; lia]. }
  clear Hr. cbn [seq map] in Hin.
  repeat (destruct Hin as [<- | Hin]; [apply bv_eq; vm_compute; reflexivity |]). destruct Hin.
Qed.

Lemma k7_beq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold branch_taken, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Lemma k7_bne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y).
Proof.
  intros x y Hx Hy. change BC_NE with (neg_bc BC_EQ). rewrite branch_taken_neg, k7_beq by assumption. reflexivity.
Qed.

Lemma k7_blt : forall a b, 0 <= a < 8 -> 0 <= b < 8 -> a < b ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof.
  intros a b Ha Hb Hab.
  assert (Ga : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7) by lia.
  assert (Gb : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7) by lia.
  clear Ha Hb.
  destruct Ga as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    destruct Gb as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    first [exfalso; lia | vm_compute; reflexivity].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis KI : KernImg pa_segs B.
Hypothesis TB : AF0m.PcapSyms B.     (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)

Definition k7a_E (ms : machine_state) (p n s b : Z) : env :=
  Eimg (Ereg (ms_regs ms) [w64 p; w64 n; w64 (SHADOW_OFF + p / 8); w64 s; w64 b]).

Lemma k7a_E_reg : forall ms p n s b (jj : nat) (r : bv 5), Z.of_nat jj = bv_unsigned r ->
  ew (k7a_E ms p n s b) jj = getr (ms_regs ms) r.
Proof. intros ms p n s b jj r H. unfold k7a_E. apply ew_Eimg_Ereg_nat. exact H. Qed.

Lemma k7a_E_ext : forall ms p n s b,
  ew (k7a_E ms p n s b) 32%nat = w64 p /\ ew (k7a_E ms p n s b) 33%nat = w64 n /\
  ew (k7a_E ms p n s b) 34%nat = w64 (SHADOW_OFF + p / 8) /\ ew (k7a_E ms p n s b) 35%nat = w64 s /\
  ew (k7a_E ms p n s b) 36%nat = w64 b.
Proof.
  intros ms p n s b. unfold k7a_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
  split; [exact (ew_Ereg_extra _ _ 0)|]. split; [exact (ew_Ereg_extra _ _ 1)|].
  split; [exact (ew_Ereg_extra _ _ 2)|]. split; [exact (ew_Ereg_extra _ _ 3) | exact (ew_Ereg_extra _ _ 4)].
Qed.

Lemma k7a_E_agree : forall ms p n s b,
  YP06.env_agree 32 (Ereg (ms_regs ms) [w64 p; w64 n; w64 (SHADOW_OFF + p / 8); w64 s; w64 b]) (k7a_E ms p n s b).
Proof. intros ms p n s b. unfold k7a_E. split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* the registers a run does not write: the same symbolic value at its start and at its end *)
Lemma k7_reg_same : forall E ss0 ss1 (H : word -> bool) (ms0 ms1 : machine_state) (l : list Z),
  st_ok_pi pa_segs pa_val E ss0 (restrict H ms0) -> st_ok_pi pa_segs pa_val E ss1 (restrict H ms1) ->
  forallb (fun k => sv_eqb (sr_get (ss_regs ss1) (Z_to_bv 5 k)) (sr_get (ss_regs ss0) (Z_to_bv 5 k))) l = true ->
  forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) l = true -> getr (ms_regs ms1) r = getr (ms_regs ms0) r.
Proof.
  intros E ss0 ss1 H ms0 ms1 l HS0 HS1 Hl r Hr.
  apply existsb_exists in Hr as (k & Hk & Hrk). apply Z.eqb_eq in Hrk.
  rewrite forallb_forall in Hl. pose proof (Hl k Hk) as Hs. apply sv_eqb_eq in Hs.
  assert (Er : r = Z_to_bv 5 k) by (rewrite <- Hrk; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite (st_ok_pi_restrict_reg H E ss1 ms1 r HS1), (st_ok_pi_restrict_reg H E ss0 ms0 r HS0), Er, Hs.
  reflexivity.
Qed.

(* the slots of the attribute loop's cuts lie in [s1 + 0x18, s1 + 0xf8) *)
Lemma k7_sl_bounds : forall cx fpos c ci m k hd kd ov,
  In ov (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)]) ->
  0x18 <= fst ov <= 0xf0.
Proof.
  intros cx fpos c ci m k hd kd ov Hov. apply in_app_or in Hov. destruct Hov as [Hov | Hov].
  - unfold kslots_setup in Hov. cbn [In] in Hov.
    repeat (destruct Hov as [<- | Hov];
      [cbv [fst KS_FSH KS_FRES KS_W1F KS_F KS_GNL KS_W1 KS_W1N KS_W1SH KS_NW KS_C KS_GQ KS_W2SH KS_MASK KS_CN
            KS_M6 KS_CSH KS_W2F KS_M4098 KS_M4093 KS_F2]; lia |]).
    destruct Hov.
  - cbn [In] in Hov.
    repeat (destruct Hov as [<- | Hov]; [cbv [fst KS_ROOM KS_CI KS_M KS_K KS_HD KS_KD]; lia |]).
    destruct Hov.
Qed.

(* the private cut at +0x9bc: a0 = b, the cursor at adv + 1 *)
Definition k7_c9bc (Rc Rm : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv hd kd b, Rc cx (c - ci) /\ Rm cx (m - k) /\
  1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= m <= 5 /\ 0 <= k < m /\ (kd = 0 \/ kd = 7) /\ 0 <= hd <= n /\
  0 <= b < 256 /\
  kw_at W3 ms3 (kW2 cx fpos) n f /\
  kat B cx fpos KP_K9BC
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (10%nat, b)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* the cursor's bytes may be written: the call's ajw, moved to the cut's journal (kernel_msg0_c.v mc_awr_cur) *)
Lemma k7_awr_cur : forall cx fpos k2 ly3 S3 W3 mm md3, kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 ->
  forall a, ka0 cx <= a < ka0 cx + 16 ->
  (awr_byte (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3
     ((KN_CID, fpos) :: k_own cx) a /\ ~ (k_sp0 cx <= a < k_sp0 cx + k_XO cx)) \/
  inG (k_G cx) a \/ (inFP (k_OUT cx) a /\ k_sp0 cx <= a < k_sp0 cx + k_XO cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 mm md3 HB HJ HJB a Ha.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  pose proof HJB as (_ & _ & Hperm & _).
  assert (HE : inFP (kernel_awr (k_regs cx) (km0 cx)) a).
  { exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16). split; [unfold kernel_awr; km_inl |].
    cbn [fst snd]. unfold ka0 in Ha. lia. }
  destruct (Hajw a HE) as [[Haw Hnout] | [HGa | Hout]]; [left; split; [|exact Hnout] | right; left; exact HGa |
    right; right; exact Hout].
  destruct Haw as [Hw | [(Hfp & b0 & n0 & Hbn & Hr) | [(b0 & n0 & Hbn & Hnb & Hr) | (cid & pos & Hown & Hr)]]].
  - left. exact Hw.
  - right; left. split; [exact Hfp|]. exists b0, n0. split; [|exact Hr].
    exact (Permutation_in _ (Permutation_sym Hperm) Hbn).
  - right; right; left. exists b0, n0. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hbn)|].
    split; [exact Hnb | exact Hr].
  - right; right; right. exists cid, pos. split; [right; exact Hown|].
    rewrite (km_fa SK B cx fpos k2 ly3 S3 W3 mm md3 HB HJ). exact Hr.
Qed.

(* THE CUT AFTER A RUN that wrote the cursor only (kernel_msg0_c.v mc_land with no slot): the cursor restated *)
Lemma k7_land : forall cx fpos pc rl sl sh adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl' adv',
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh true adv g k2 ly3 S3 W3 ms3 md3 ->
  (length sh <= 2048)%nat -> (forall ov, In ov sl -> 0x18 <= fst ov <= 0xf0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  kms pc' ms' -> kregs0 cx ms' -> kregs_eq ms' rl' -> kcursor cx W3 ms' adv' ->
  kat B cx fpos pc' rl' sl sh true adv' g k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos pc rl sl sh adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl' adv'
    HB HK Hsh Hsl UN HP Hfds Hfs Hkms Hr0 Hrl Hcur.
  pose proof HK as (_ & _ & _ & HSAV & HFR & HSH & HSL & HJB & HKEPT & _ & HGNL & HLA).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1.
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & _ & F5 & _).
  rewrite kn_fsb8 in F2, F3, F5. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  pose proof (kn_apre SK B cx HB) as (AG & AL & _).
  unfold apart_gnl, apart in AG, AL.
  set (X := fun a => ka0 cx <= a < ka0 cx + 16).
  assert (UNX : forall a, 0 <= a < 2 ^ 64 -> ~ X a ->
            aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) by exact UN.
  assert (CW : forall a, X a ->
            ~ (ksp cx - 4640 <= a < ksp cx) /\ (a < kLowMemEnd \/ kHighMemBeg <= a) /\
            ~ (kF cx fpos <= a < kF cx fpos + 16384)).
  { intros a Ha. unfold X in Ha. destruct (CL a Ha) as (CL1 & CL2). rewrite HK8 in CL2.
    split; [exact CL2|]. split; [exact CL1|].
    assert (Hx : kernel_ard SEGS (k_regs cx) (km0 cx) a) by (left; unfold ka0 in Ha; exact Ha).
    pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB Hx) as HnF. rewrite kn_fsb8 in HnF. exact HnF. }
  unfold kat.
  refine (conj Hkms (conj Hr0 (conj Hrl (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hcur
    (conj _ _))))))))))).
  - apply (ksaved_frame SK B X cx W3 ms3 W3 ms' HB UNX); [|exact HSAV].
    intros a Ha Hx. destruct (CW a Hx) as (CW1 & _). lia.
  - apply (kframe_frame B LAWS X cx fpos true k2 ly3 S3 md3 W3 ms3 W3 ms' HJB UNX HP); [| | exact HFR];
      rewrite ?kn_fsb8; intros a Ha Hx; destruct (CW a Hx) as (_ & _ & CW3); lia.
  - apply (kshadow_frame B LAWS X cx fpos sh k2 ly3 S3 md3 W3 ms3 W3 ms' HJB UNX Hsh); [|exact HSH].
    intros a Ha Hx. destruct (CW a Hx) as (_ & CW2 & _).
    unfold kFSH, shadow_of_addr, kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia.
  - apply (kslots_frame SK B X cx sl sl W3 ms3 W3 ms' HB UNX (incl_refl _)); [|exact HSL].
    intros ov Hov. destruct (Hsl ov Hov) as (Ho1 & Ho2). split; [lia|].
    intros a Ha Hx. destruct (CW a Hx) as (CW1 & _). lia.
  - exact (kjbk_md B cx fpos k2 ly3 S3 md3 md' HJB Hfds Hfs).
  - apply (kkept_frame SK B LAWS X cx fpos k2 ly3 S3 md3 W3 ms3 W3 ms' HB HJB UNX HP); [|exact HKEPT].
    intros a Hx. unfold kX_in. left. unfold kE, inFP. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
    split; [unfold kernel_awr; km_inl | cbn [fst snd]; unfold X, ka0 in Hx; exact Hx].
  - apply (kgnl_frame X cx g W3 ms3 W3 ms' UNX HP); [|exact HGNL].
    intros a Ha Hx. unfold X in Hx. unfold LA_G_NL, NK_SIZE in *. lia.
  - apply (kla_frame X W3 ms3 W3 ms' UNX HP); [|exact HLA].
    intros a Ha Hx. unfold X in Hx. unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in *. lia.
Qed.

(* the cut after a run with no writable window: the same memory *)
Lemma k7_land0 : forall cx fpos pc rl sl adv j k2 ly3 S3 W3 ms3 md3 pc' rl' (E : env) ss (ms : machine_state) md,
  kbase SK B cx ->
  kat B cx fpos pc rl sl (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  kslots_okb sl = true ->
  (forall bb wlo whi x, In (bb, wlo, whi) (windows (ss_mem ss)) -> base_val E bb + wlo <= x < base_val E bb + whi ->
     False) ->
  frame_of E (ss_mem ss) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  kms pc' ms -> kregs0 cx ms -> kregs_eq ms rl' ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  kat B cx fpos pc' rl' sl (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms md.
Proof.
  intros cx fpos pc rl sl adv j k2 ly3 S3 W3 ms3 md3 pc' rl' E ss ms md HB HAT Hok Hw HFr HG HMS HR0 HRL Hfds Hfs.
  apply (kat_frame_w2 SK B LAWS 0 0 cx fpos pc rl sl _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 pc' rl' sl
           W3 ms md HB HAT HMS HR0 HRL (fun x Hx => Hx) Hok (kfsh_fits _ _ _) Hfds Hfs ltac:(lia)
           ltac:(unfold NW_SIZE; lia)).
  - intros q Hq _.
    apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms) (fun _ => False) HFr);
      [| exact Hq | intros []].
    intros b wlo whi x Hin Hx. exact (Hw b wlo whi x Hin Hx).
  - intros q Hq. exact (k3_apres_grows _ _ _ q HG Hq).
Qed.

(* w2 is kept when only the cursor changed *)
Lemma k7_kw_keep : forall cx fpos k2 ly3 S3 md3 W3 ms3 ms' n f,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  kw_at W3 ms' (kW2 cx fpos) n f.
Proof.
  intros cx fpos k2 ly3 S3 md3 W3 ms3 ms' n f HB HJB HW UN HP.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _).
  apply (kn_kw_keep W3 ms3 ms' _ n f HW); [|exact HP].
  intros i Hi. unfold kW2, KN_W2, NW_SIZE in *. apply UN; [lia|].
  intros Hx.
  assert (Hx' : kernel_ard SEGS (k_regs cx) (km0 cx) (kF cx fpos + 0x1130 + i)) by (left; unfold ka0 in Hx; exact Hx).
  pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 _ HB HJB Hx') as HnF. rewrite kn_fsb8 in HnF. lia.
Qed.

(* ======================================== (A1) ======================================== *)

(* n = 0: +0x96c `ld a0, 0(s3); beqz a0` -> +0x106c *)
Lemma k7a_zero : forall POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd,
  kfrom SK B POST (kin_nlend B Rc Rm) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) ->
  1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m -> (kd = 0 \/ kd = 7) -> 0 <= hd <= n ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K960
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, m)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  k_wn cx - adv = 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd HN HB HJ HFR HRc HRm Hc Hci Hj Hm Hk Hkd
    Hhd HW HAT Hn0.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & HKK & HCUR & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  destruct HCUR as (Hadv0 & HCP & HCN & HCW).
  pose proof HB as ((_ & HGok & _) & _).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  pose proof (kn_reg_of ms3 _ 19 (ka0 cx + 8) HRL ltac:(kn_in)) as R19.
  pose proof (kn_reg_of ms3 _ 24 (kS8 cx) HRL ltac:(kn_in)) as R24.
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) []) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E18 : ew E 18%nat = w64 (ka0 cx)) by (rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 18 18%bv eq_refl); exact A18).
  assert (E9 : ew E 9%nat = w64 (ksp1 cx)) by (rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 9 9%bv eq_refl); exact A9).
  assert (E20 : ew E 20%nat = w64 SHADOW_OFF) by (rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 20 20%bv eq_refl); exact A20).
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (apply km_bv; [exact E18 | lia]).
  assert (HS : st_ok_pi SEGS pa_val E k7z_ss (restrict (w_H W3) ms3)).
  { rewrite (kn_ms_shape ms3 (BASE + kpc KP_K960) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx. unfold k7z_ss.
    apply pa_entry_st_ok_full.
    - unfold km_regsA.
      apply kn_regs_ok_set; [apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |]
                            | vm_compute; reflexivity |].
      + cbn [sv_denot]. rewrite BV18. exact (eq_sym R19).
      + rewrite (km_denot_sh E 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20). exact (eq_sym R24).
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold k7z_cur, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite BV18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      rewrite <- Hn0. exact HCN.
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - exact (km_facts SK B LAWS cx fpos k2 ly3 S3 md3 E HB HJB E18 E9 E20). }
  pose proof HS as HS0.
  pose proof (km_shok SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 E HB HJ HJB HKK E18 E20) as SHOK.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK km_span (kpc KP_NLEND).
  { apply awr_ok_x_cons; [intros a Ha; cbn [k7z_cur YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_nil. }
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn),
    HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
    HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    pose proof (k7_reg_same E k7z_ss ssx (w_H W3) ms3 msn [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25] HS0 HS'
                  ltac:(vm_compute; reflexivity)) as KEEP;
    assert (HKMS : kms KP_NLEND msn) by (apply (kn_kms_of _ E ssx msn KP_NLEND HS'); vm_compute; reflexivity);
    assert (UN : forall a, 0 <= a < 2 ^ 64 ->
                   aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
      by (intros a Ha;
          apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem msn) (fun _ => False) HFr');
          [ intros bb wlo whi x Hin; unfold k7z_ss, windows in Hin;
            cbn [ss_mem map In k7z_cur YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
            destruct Hin as [Hq | []]; injection Hq as <- <- <-; lia
          | exact Ha | intros []]);
    assert (HP : forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem msn) a)
      by (intros a Ha; exact (k3_apres_grows _ _ _ a HG' Ha));
    apply (HN cx fpos k2 ly3 S3 W3 msn mdn HB ltac:(assumption) HFR);
    exists c, ci, j, m, k, n, f, adv, hd, kd;
    split; [exact HRc|]; split; [exact HRm|]; split; [exact Hc|]; split; [exact Hci|]; split; [exact Hj|];
    split; [exact Hm|]; split; [exact Hk|]; split; [exact Hkd|]; split; [exact Hhd|];
    split; [exact (k7_kw_keep cx fpos k2 ly3 S3 md3 W3 ms3 msn n f HB HJB HW (fun a Ha _ => UN a Ha) HP)|];
    apply (kat_frame_w2 SK B LAWS 0 0 cx fpos KP_K960 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 KP_NLEND _ _
             W3 msn mdn HB HAT HKMS);
    [ unfold kregs0; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
        rewrite KEEP by reflexivity; assumption
    | unfold kregs_eq; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        rewrite KEEP by reflexivity; apply (kn_reg_of ms3 _ _ _ HRL); kn_in
    | intros x Hx; apply in_app_or in Hx; apply in_or_app; destruct Hx as [Hx|Hx]; [left; exact Hx | right; exact Hx]
    | reflexivity
    | apply kfsh_fits
    | exact (proj1 (wvb_fds_fs _ _ _))
    | exact (proj2 (wvb_fds_fs _ _ _))
    | lia
    | unfold NW_SIZE; lia
    | intros q Hq _; exact (UN q Hq)
    | exact HP ]
  end.
Qed.

(* the state at +0x960, n >= 1: the two cases of the input byte's shadow byte s *)
Lemma k7a_seat : forall cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv j (fast : bool) s (b : byte),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kat B cx fpos KP_K960 rl sl (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  In (19%nat, ka0 cx + 8) rl -> In (24%nat, kS8 cx) rl -> In (KS_CSH, shadow_of_addr SHADOW_OFF (ka0 cx)) sl ->
  adv < k_wn cx ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s ->
  saddr_ok (k_wp cx + adv) s ->
  mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (k_wp cx + adv) = Some b ->
  (if fast then s = 0 else s <> 0) ->
  st_ok_pi SEGS pa_val (k7a_E ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) (k7a_ss fast)
    (restrict (w_H W3) ms3).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv j fast s b HB HJ HK I19 I24 ICSH Hadv Hs Hsok Hb Hf.
  pose proof HK as (Hkms & Hkr0 & Hkre & _ & _ & _ & Hksl & HJB & _ & Hkcur & _ & _).
  destruct Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  destruct Hkcur as (Hadv0 & HCP & HCN & HCW).
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & HAP).
  destruct HAP as (HAPF & HAPG & HAPL & HAPC).
  unfold apart_frame, apart in HAPF, HAPC. change (spZ (k_regs cx)) with (ksp cx) in HAPF.
  change (aarg (k_regs cx) 0) with (ka0 cx) in HAPC.
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & S6 & S7 & S8 & S9 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1, S6, HAPF.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  pose proof (proj2 (CL (ka0 cx) ltac:(lia))) as CLa. pose proof (proj2 (CL (ka0 cx + 15) ltac:(lia))) as CLb.
  rewrite HK8 in CLa, CLb.
  pose proof (proj1 (CL (ka0 cx) ltac:(lia))) as CAa. pose proof (proj1 (CL (ka0 cx + 15) ltac:(lia))) as CAb.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv + 1 <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  assert (Hpard : kernel_ard SEGS (k_regs cx) (km0 cx) (k_wp cx + adv)).
  { pose proof HB as (_ & _ & _ & _ & _ & HWP & HWN & _).
    unfold kernel_ard. right. left. exists (k_wp cx), (k_wn cx). unfold ka0 in *.
    refine (conj HWP (conj HWN (conj HWPr (conj HWNr _)))). lia. }
  destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 _ HB HJB Hpard) as (PL1 & PL2 & _ & PL4).
  pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  unfold aview in Hs.
  destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)))
    as [bs|] eqn:Ebs; [|discriminate Hs].
  cbn [option_map] in Hs. assert (Hs' : bv_unsigned bs = s) by (injection Hs; auto). clear Hs.
  assert (Hsr : 0 <= s < 8) by (pose proof (bv_unsigned_in_range 8 bs); unfold saddr_ok in Hsok; lia).
  pose proof (kn_reg_of ms3 rl 19 _ Hkre I19) as R19.
  pose proof (kn_reg_of ms3 rl 24 _ Hkre I24) as R24.
  destruct Hkr0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  destruct (k7a_E_ext ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) as (E32 & E33 & E34 & E35 & E36).
  assert (E18 : ew (k7a_E ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) 18%nat = w64 (ka0 cx))
    by (rewrite (k7a_E_reg _ _ _ _ _ 18 18%bv eq_refl); exact A18).
  assert (E9 : ew (k7a_E ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) 9%nat = w64 (ksp1 cx))
    by (rewrite (k7a_E_reg _ _ _ _ _ 9 9%bv eq_refl); exact A9).
  assert (E20 : ew (k7a_E ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) 20%nat = w64 SHADOW_OFF)
    by (rewrite (k7a_E_reg _ _ _ _ _ 20 20%bv eq_refl); exact A20).
  remember (k7a_E ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) as E eqn:HEdef.
  set (p := k_wp cx + adv) in *.
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (apply km_bv; [exact E18 | lia]).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  assert (BV32 : bv_unsigned (ew E 32%nat) = p) by (apply km_bv; [exact E32 | lia]).
  assert (Hq : SHADOW_OFF <= SHADOW_OFF + p / 8 < SHADOW_OFF + 2 ^ 44)
    by (split; [pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); lia |
                pose proof (Z.div_lt_upper_bound p 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia]).
  assert (BV34 : bv_unsigned (ew E 34%nat) = SHADOW_OFF + p / 8) by (apply km_bv; [exact E34 | unfold SHADOW_OFF in *; lia]).
  pose proof (kn_slot_of cx W3 ms3 sl KS_CSH _ Hksl ICSH) as SL_CSH.
  rewrite (kn_ms_shape ms3 (BASE + kpc KP_K960) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  unfold k7a_ss. apply pa_entry_st_ok_full.
  - unfold km_regsA.
    apply kn_regs_ok_set; [apply kn_regs_ok_set; [subst E; unfold k7a_E; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |]
                          | vm_compute; reflexivity |].
    + cbn [sv_denot]. rewrite BV18. exact (eq_sym R19).
    + rewrite (km_denot_sh E 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20). exact (eq_sym R24).
  - destruct fast; vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold k7a_cur, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite BV18. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HCW o Ho)|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 32 0) p);
          [apply sv_off0; exact E32 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HCP].
      * apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 (SOff 33 0) (k_wn cx - adv));
          [apply sv_off0; exact E33 | cbn; lia | cbn; lia | exact HCN].
    + unfold k7a_sl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite BV9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc0 (km_sh 18 0) (shadow_of_addr SHADOW_OFF (ka0 cx)));
        [|exact SL_CSH].
      rewrite (km_denot_sh E 18 (ka0 cx) 0 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
      rewrite Z.add_0_r. reflexivity.
    + unfold k7a_in, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite BV32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ p 0 1 (SOff 36 0) (bv_unsigned b));
        [apply sv_off0; exact E36 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. intros k Hk. destruct k as [|k]; [|cbn in Hk; lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb.
      rewrite le_byte_small by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia).
      change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + unfold k7a_shr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite BV34. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (SHADOW_OFF + p / 8) 0 1 (if fast then SLit 0 else SOff 35 0) s);
        [destruct fast; [cbn in Hf; rewrite Hf; reflexivity | apply sv_off0; exact E35] | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. intros k Hk. destruct k as [|k]; [|cbn in Hk; lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
      unfold shadow_of_addr in Ebs. rewrite Ebs, <- Hs'.
      rewrite le_byte_small by (pose proof (bv_unsigned_in_range 8 bs); change (2 ^ (8 * Z.of_nat 1)) with 256;
                                change (bv_modulus 8) with 256 in *; lia).
      change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, k7a_cur, k7a_sl, k7a_in, k7a_shr. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite BV18, BV9, BV32, BV34.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *.
    repeat split; lia.
  - unfold facts_ok, k7a_facts. cbn [f_atoms f_conds f_alias]. split; [|split].
    + unfold km_atoms. destruct fast; cbv iota in Hf; cbn [app atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
        rewrite ?E18, ?E9, ?E20, ?E33, ?E36, ?E35; unfold w64;
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia);
        change (2 ^ 0) with 1; change (2 ^ 5) with 32; rewrite !Z.mod_1_r; unfold SHADOW_OFF;
        repeat split; first [lia | exact I | exact S5].
    + assert (Dslow : sv_denot E (SAlu ALU_AND (SOff 32 0) (SLit 7)) = Z_to_bv 64 (p mod 8)).
      { rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
        rewrite (U_atom_off E 32 p 0 E32 ltac:(lia) ltac:(lia)), Z.add_0_r.
        change (zcanon 7) with 7.
        assert (Hl7 : Z.land p 7 = p mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
        rewrite Hl7. apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound p 8). lia. }
      pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hm8.
      destruct fast; cbv iota in Hf; cbn [conds_ok]; [exact I|]. unfold acond_ok; cbn [ac_c ac_a ac_b].
      rewrite Dslow, (sv_off0 E 35 _ E35). split; [apply k7_blt; [lia | lia | unfold saddr_ok in Hsok; lia] | exact I].
    + cbn [alias_ok]. split; [|exact I].
      rewrite (km_denot_sh E 32 p 0 E32 ltac:(lia) ltac:(lia) ltac:(lia) E20).
      rewrite (sv_off0 E 34 _ E34). rewrite Z.add_0_r. reflexivity.
Qed.

(* the end of an (A1) run at +0x9bc: the cut k7_c9bc *)
Lemma k7a_fin : forall POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd (E : env) b,
  kfrom SK B POST (k7_c9bc Rc Rm) ->
  kbase SK B cx ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) ->
  1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m -> (kd = 0 \/ kd = 7) -> 0 <= hd <= n ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K960
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, m)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  adv < k_wn cx -> 0 <= b < 256 ->
  bv_unsigned (ew E 18%nat) = ka0 cx -> bv_unsigned (ew E 32%nat) = k_wp cx + adv ->
  bv_unsigned (ew E 33%nat) = k_wn cx - adv -> bv_unsigned (ew E 36%nat) = b ->
  forall (ms : machine_state) md cs',
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 18%nat) 0 16 0 16 cs') ->
  In (YP09.mkChunk 0 (CVal 8 (SOff 32 1))) cs' -> In (YP09.mkChunk 8 (CVal 8 (SOff 33 (-1)))) cs' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  kms KP_K9BC ms ->
  (forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25] = true ->
     getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 10)) = sv_denot E (SOff 36 0) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd E b HN HB HFR HRc HRm Hc Hci Hj
    Hm Hk Hkd Hhd HW HAT Hadv Hbr BV18 BV32 BV33 BV36 ms md cs' HRC Hin0 Hin8 UN HG HJ HKMS KEEP H10 Hfds Hfs.
  pose proof HAT as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _ & HCUR & _).
  destruct HCUR as (Hadv0 & HCP & HCN & HCW).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv + 1 <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  assert (HP : forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms) a)
    by (intros a Ha; exact (k3_apres_grows _ _ _ a HG Ha)).
  assert (DP1 : sv_denot E (SOff 32 1) = Z_to_bv 64 (k_wp cx + (adv + 1))).
  { cbn [sv_denot]. rewrite BV32. f_equal. lia. }
  assert (DN1 : sv_denot E (SOff 33 (-1)) = Z_to_bv 64 (k_wn cx - (adv + 1))).
  { cbn [sv_denot]. rewrite BV33. f_equal. lia. }
  pose proof (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 1) _ HRC BV18
    Hin0 DP1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia)) as VP.
  pose proof (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SOff 33 (-1)) _ HRC BV18
    Hin8 DN1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia)) as VN.
  assert (HCUR' : kcursor cx W3 ms (adv + 1)).
  { split; [lia|]. split; [rewrite Z.add_0_r in VP; exact VP|]. split; [exact VN|].
    intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (HCW i Hi)). }
  assert (HR0' : kregs0 cx ms).
  { unfold kregs0. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite KEEP by reflexivity; assumption. }
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  exists c, ci, j, m, k, n, f, (adv + 1), hd, kd, b.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|]. split; [exact Hhd|]. split; [exact Hbr|].
  split; [exact (k7_kw_keep cx fpos k2 ly3 S3 md3 W3 ms3 ms n f HB HJB HW UN HP)|].
  apply (k7_land cx fpos KP_K960 _ _ _ adv (Some j) k2 ly3 S3 W3 ms3 md3 ms md KP_K9BC _ (adv + 1) HB HAT).
  - rewrite kfsh_length. lia.
  - intros ov Hov. exact (k7_sl_bounds cx fpos c ci m k hd kd ov Hov).
  - exact UN.
  - exact HP.
  - exact Hfds.
  - exact Hfs.
  - exact HKMS.
  - exact HR0'.
  - unfold kregs_eq. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    1-4: rewrite KEEP by reflexivity; apply (kn_reg_of ms3 _ _ _ HRL); kn_in.
    rewrite H10. cbn [sv_denot]. rewrite BV36, Z.add_0_r. reflexivity.
  - exact HCUR'.
Qed.

(* one (A1) run, n >= 1 (the shadow case fast given) *)
Ltac k7a_run HSEAT HJ SHOK RUNTO KFIN E cx fpos k2 ly3 S3 W3 ms3 md3 HB HJB BV18 BV9 :=
  let HS := fresh "HS" in
  pose proof HSEAT as HS;
  paj_run_to_tok RUNTO HS HJ SHOK km_span (kpc KP_K9BC);
  [ apply awr_ok_x_cons;
      [ intros a Ha; cbn [k7a_cur YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite BV18 in Ha;
        exact (k7_awr_cur cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ HJB a ltac:(lia)) |];
    apply awr_ok_x_cons; [intros a Ha; cbn [k7a_sl YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|];
    apply awr_ok_x_cons; [intros a Ha; cbn [k7a_in YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|];
    apply awr_ok_x_cons; [intros a Ha; cbn [k7a_shr YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|];
    apply awr_ok_x_nil
  | ];
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn),
    HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
    HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    let HRC := fresh "HRC" in
    spregion HS' 0%nat HRC;
    apply (KFIN msn mdn _ HRC ltac:(km_inl) ltac:(km_inl));
    [ intros a Ha Hna;
      apply (kept_of_frame (segs := pa_segs) E _ _ _ _ (fun x => ka0 cx <= x < ka0 cx + 16) HFr');
      [ intros bb wlo whi x Hin Hx; unfold k7a_ss, windows in Hin;
        cbn [ss_mem map In k7a_cur k7a_sl k7a_in k7a_shr YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
        destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-; cbn [base_val] in Hx; cbv beta;
        [rewrite BV18 in Hx; lia | lia | lia | lia]
      | exact Ha | exact Hna ]
    | exact HG'
    | assumption
    | apply (kn_kms_of _ E ssx msn KP_K9BC HS'); vm_compute; reflexivity
    | exact (k7_reg_same E _ ssx (w_H W3) ms3 msn [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25] HSEAT HS'
               ltac:(vm_compute; reflexivity))
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | exact (proj1 (wvb_fds_fs _ _ _))
    | exact (proj2 (wvb_fds_fs _ _ _)) ]
  end.

(* ---- (A1) THE PHASE ---- *)
Theorem k7a_p1 : forall POST (Rc Rm : kcx -> Z -> Prop),
  kfrom SK B POST (k7_c9bc Rc Rm) -> kfrom SK B POST (kin_nlend B Rc Rm) -> kfrom SK B POST (k7_c960 B Rc Rm).
Proof.
  intros POST Rc Rm HN9 HNLE cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (c & ci & j & m & k & n & f & adv & hd & kd & HRc & HRm & Hc & Hci & Hj & Hm & Hk & Hkd & Hhd & HW
    & HAT).
  pose proof HAT as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & HKK & HCUR & _).
  destruct HCUR as (Hadv0 & _).
  destruct (Z.eq_dec (k_wn cx - adv) 0) as [Hn0 | Hn1].
  { exact (k7a_zero POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd HNLE HB HJ HFR HRc HRm Hc Hci
             Hj Hm Hk Hkd Hhd HW HAT Hn0). }
  assert (Hadv : adv < k_wn cx) by lia.
  pose proof HB as (HPRE & _ & _ & _ & _ & HWP & HWN & HWPr & HWNr & HD & HDL & _).
  pose proof HPRE as (_ & HGok & _).
  destruct (kn_input_at SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 (k_wp cx + adv) HB HJ HJB HKK ltac:(lia))
    as ((s & Hs & Hsok) & Hview).
  destruct HD as (_ & _ & HD).
  assert (Hi : (Z.to_nat adv < length (k_d cx))%nat) by lia.
  destruct (nth_error (k_d cx) (Z.to_nat adv)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  pose proof (HD (Z.to_nat adv) Hi) as Hmb. rewrite Eb, Z2Nat.id in Hmb by lia.
  assert (Hb : mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (k_wp cx + adv) = Some b).
  { rewrite <- Hmb. exact (mbyte_of_aview SEGS (w_H (k_W cx)) (w_H W3) (k_memc cx) (ms_mem ms3) _ Hview). }
  pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv + 1 <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  destruct (k7a_E_ext ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) as (E32 & E33 & E34 & E35 & E36).
  assert (E18 : ew (k7a_E ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) 18%nat = w64 (ka0 cx))
    by (rewrite (k7a_E_reg _ _ _ _ _ 18 18%bv eq_refl); exact A18).
  assert (E9 : ew (k7a_E ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) 9%nat = w64 (ksp1 cx))
    by (rewrite (k7a_E_reg _ _ _ _ _ 9 9%bv eq_refl); exact A9).
  assert (E20 : ew (k7a_E ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) 20%nat = w64 SHADOW_OFF)
    by (rewrite (k7a_E_reg _ _ _ _ _ 20 20%bv eq_refl); exact A20).
  pose proof (k7a_E_agree ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) as HAG.
  remember (k7a_E ms3 (k_wp cx + adv) (k_wn cx - adv) s (bv_unsigned b)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx).
  { apply km_bv; [exact E18|]. destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & _). lia. }
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx).
  { apply km_bv; [exact E9|]. pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _).
    pose proof asan_consts as ((C1a & C1b) & _).
    assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1. lia. }
  assert (BV32 : bv_unsigned (ew E 32%nat) = k_wp cx + adv) by (apply km_bv; [exact E32 | lia]).
  assert (BV33 : bv_unsigned (ew E 33%nat) = k_wn cx - adv) by (apply km_bv; [exact E33 | lia]).
  assert (BV36 : bv_unsigned (ew E 36%nat) = bv_unsigned b) by (apply km_bv; [exact E36 | lia]).
  pose proof (km_shok SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 E HB HJ HJB HKK E18 E20) as SHOK.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose proof (k7a_fin POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd E (bv_unsigned b) HN9 HB HFR
                HRc HRm Hc Hci Hj Hm Hk Hkd Hhd HW HAT Hadv Hbr BV18 BV32 BV33 BV36) as KF.
  destruct (Z.eq_dec s 0) as [Hs0 | Hs0].
  - pose proof (k7a_seat cx fpos k2 ly3 S3 W3 ms3 md3 _ _ adv j true s b HB HJ HAT ltac:(kn_in) ltac:(kn_in)
                  ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) Hadv Hs Hsok Hb Hs0) as HSEAT.
    rewrite <- HEdef in HSEAT.
    k7a_run HSEAT HJ SHOK RUNTO KF E cx fpos k2 ly3 S3 W3 ms3 md3 HB HJB BV18 BV9.
  - pose proof (k7a_seat cx fpos k2 ly3 S3 W3 ms3 md3 _ _ adv j false s b HB HJ HAT ltac:(kn_in) ltac:(kn_in)
                  ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) Hadv Hs Hsok Hb Hs0) as HSEAT.
    rewrite <- HEdef in HSEAT.
    k7a_run HSEAT HJ SHOK RUNTO KF E cx fpos k2 ly3 S3 W3 ms3 md3 HB HJB BV18 BV9.
Qed.

(* ======================================== (A2) ======================================== *)

(* the multiplier's word: its address the image's, its value KI's *)
Lemma k7m_seat : forall cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv g b (zero : bool),
  kat B cx fpos KP_K9BC rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 ->
  In (10%nat, b) rl -> 0 <= b < 256 ->
  (if zero then b mod 5 = 0 else b mod 5 <> 0) ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) [])) (k7m_ss zero) (restrict (w_H W3) ms3).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv g b zero HK I10 Hbr Hz.
  pose proof HK as (Hkms & _ & Hkre & _ & _ & _ & _ & _ & HKK & _).
  destruct Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  destruct HKK as (_ & HRO).
  pose proof (kn_reg_of ms3 rl 10 _ Hkre I10) as R10.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (E10 : ew E 10%nat = Z_to_bv 64 b) by (rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 10 (Z_to_bv 5 (Z.of_nat 10)) eq_refl);
                                               exact R10).
  assert (BVK : base_val E (Some (A_OBJ 17)) = 0x10310).
  { cbn [base_val]. rewrite HEdef, Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj LV 17%nat) by (unfold link_nobj; lia).
    change (link_obj 17) with 0x10310. apply unsigned_lit_small. lia. }
  rewrite (kn_ms_shape ms3 (BASE + kpc KP_K9BC) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  unfold k7m_ss. apply pa_entry_st_ok_full.
  - rewrite HEdef. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold k7m_rg, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BVK. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ 0x10310 0 8 (SLit KI_M5_V) KI_M5_V); [reflexivity | unfold KI_M5_V; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (ki_m5_val_mem SEGS PCAP_RLO PCAP_RHI B KI (w_H W3) (ms_mem ms3) HRO).
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I|]. split; [|exact I]. split; [|exact I].
    unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite (k7_m5_val E b E10 Hbr).
    change (sv_denot E (SLit 0)) with (Z_to_bv 64 0).
    pose proof (Z.mod_pos_bound b 5 ltac:(lia)) as Hm5.
    destruct zero; [rewrite k7_beq by lia; apply Z.eqb_eq; lia | rewrite k7_bne by lia; apply negb_true_iff, Z.eqb_neq; lia].
Qed.

(* ---- (A2) THE PHASE ---- *)
Theorem k7m_p : forall POST (Rc Rm Ra : kcx -> Z -> Prop),
  (forall cx v, 1 <= v <= 4 -> Ra cx v) ->
  kfrom SK B POST (kin_attr B Rc Rm Ra) -> kfrom SK B POST (kin_nlend B Rc Rm) -> kfrom SK B POST (k7_c9bc Rc Rm).
Proof.
  intros POST Rc Rm Ra HRa HATT HNLE cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (c & ci & j & m & k & n & f & adv & hd & kd & b & HRc & HRm & Hc & Hci & Hj & Hm & Hk & Hkd & Hhd
    & Hbr & HW & HAT).
  pose proof HAT as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof (kn_reg_of ms3 _ 10 b HRL ltac:(kn_in)) as R10.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) []) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E10 : ew E 10%nat = Z_to_bv 64 b) by (rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 10 (Z_to_bv 5 (Z.of_nat 10)) eq_refl);
                                               exact R10).
  assert (SHOK : sh_ok SEGS km_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  assert (Hok : kslots_okb (kslots_setup cx fpos c ++
                  [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)]) = true)
    by reflexivity.
  assert (HKW : forall (ms : machine_state) ss,
            (forall bb wlo whi x, In (bb, wlo, whi) (windows (ss_mem ss)) ->
               base_val E bb + wlo <= x < base_val E bb + whi -> False) ->
            frame_of E (ss_mem ss) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
            mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
            kw_at W3 ms (kW2 cx fpos) n f).
  { intros ms ss Hw HFn HGn. apply (kn_kw_keep W3 ms3 ms (kW2 cx fpos) n f HW).
    - intros i Hi.
      apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms) (fun _ => False) HFn).
      + intros bb wlo whi x Hin Hx. exact (Hw bb wlo whi x Hin Hx).
      + pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
        pose proof asan_consts as ((C1a & C1b) & _). unfold kW2, KN_W2, NW_SIZE in *. lia.
      + intros [].
    - intros q Hq. exact (k3_apres_grows _ _ _ q HGn Hq). }
  assert (HW0 : forall (z : bool) bb wlo whi x, In (bb, wlo, whi) (windows (ss_mem (k7m_ss z))) ->
            base_val E bb + wlo <= x < base_val E bb + whi -> False).
  { intros z bb wlo whi x Hin Hx. unfold k7m_ss, windows in Hin.
    cbn [ss_mem map In k7m_rg YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    destruct Hin as [Hq | []]; injection Hq as <- <- <-. lia. }
  (* the registers the run keeps: s3, s5, s8, s9 *)
  assert (HKP : forall (msn : machine_state) ssx,
            st_ok_pi SEGS pa_val E ssx (restrict (w_H W3) msn) ->
            forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssx) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
              (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 25]%nat) = true ->
            forall r : nat, In r [19; 21; 24; 25]%nat ->
            getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))).
  { intros msn ssx HSx Hb r Hr. exact (regs_kept_of_st_ok_pi E ssx _ _ _ _ HSx HAG Hb _ (kn_in_map5 r _ Hr)). }
  destruct (Z.eq_dec (b mod 5) 0) as [Hz | Hz].
  - (* b % 5 = 0: nl_end *)
    pose proof (k7m_seat cx fpos k2 ly3 S3 W3 ms3 md3 _ _ adv (Some j) b true HAT ltac:(kn_in) Hbr Hz) as HS.
    rewrite <- HEdef in HS. pose proof HS as HS0.
    paj_run_to_tok RUNTO HS HJ SHOK km_span (kpc KP_NLEND).
    { apply awr_ok_x_cons; [intros a Ha; cbn [k7m_rg YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_nil. }
    lazymatch goal with
    | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn),
      HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      apply (HNLE cx fpos k2 ly3 S3 W3 msn mdn HB ltac:(assumption) HFR);
      exists c, ci, j, m, k, n, f, adv, hd, kd;
      split; [exact HRc|]; split; [exact HRm|]; split; [exact Hc|]; split; [exact Hci|]; split; [exact Hj|];
      split; [exact Hm|]; split; [exact Hk|]; split; [exact Hkd|]; split; [exact Hhd|];
      split; [exact (HKW msn (k7m_ss true) (HW0 true) HFr' HG')|];
      apply (k7_land0 cx fpos KP_K9BC _ _ adv j k2 ly3 S3 W3 ms3 md3 KP_NLEND _ E (k7m_ss true) msn mdn HB HAT Hok
               (HW0 true) HFr' HG');
      [ apply (kn_kms_of _ E ssx msn KP_NLEND HS'); vm_compute; reflexivity
      | exact (kregs0_keep cx ms3 msn
                 (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity)) HR0)
      | unfold kregs_eq; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          lazymatch goal with |- getr (ms_regs _) (Z_to_bv 5 (Z.of_nat ?r)) = w64 _ =>
            rewrite (HKP msn ssx HS' ltac:(vm_compute; reflexivity) r ltac:(kn_in));
            apply (kn_reg_of ms3 _ r _ HRL); kn_in end
      | exact (proj1 (wvb_fds_fs _ _ _))
      | exact (proj2 (wvb_fds_fs _ _ _)) ]
    end.
  - (* b % 5 in 1..4: the attribute loop *)
    pose proof (k7m_seat cx fpos k2 ly3 S3 W3 ms3 md3 _ _ adv (Some j) b false HAT ltac:(kn_in) Hbr Hz) as HS.
    rewrite <- HEdef in HS. pose proof HS as HS0.
    pose proof (Z.mod_pos_bound b 5 ltac:(lia)) as Hm5.
    paj_run_to_tok RUNTO HS HJ SHOK km_span (kpc KP_ATTR).
    { apply awr_ok_x_cons; [intros a Ha; cbn [k7m_rg YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_nil. }
    lazymatch goal with
    | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn),
      HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      pose proof (st_ok_pi_restrict_reg (w_H W3) E _ msn (Z_to_bv 5 (Z.of_nat 22)) HS') as R22;
      lazymatch type of R22 with _ = sv_denot _ ?t => replace t with k7_m5 in R22 by (vm_compute; reflexivity) end;
      rewrite (k7_m5_val E b E10 Hbr) in R22;
      apply (HATT cx fpos k2 ly3 S3 W3 msn mdn HB ltac:(assumption) HFR);
      exists c, ci, j, m, k, n, f, adv, hd, kd, (b mod 5);
      split; [exact HRc|]; split; [exact HRm|]; split; [exact (HRa cx (b mod 5) ltac:(lia))|];
      split; [exact Hc|]; split; [exact Hci|]; split; [exact Hj|]; split; [exact Hm|]; split; [exact Hk|];
      split; [exact Hkd|]; split; [lia|]; split; [exact Hhd|];
      split; [exact (HKW msn (k7m_ss false) (HW0 false) HFr' HG')|]; split; [exact I|];
      apply (k7_land0 cx fpos KP_K9BC _ _ adv j k2 ly3 S3 W3 ms3 md3 KP_ATTR _ E (k7m_ss false) msn mdn HB HAT Hok
               (HW0 false) HFr' HG');
      [ apply (kn_kms_of _ E ssx msn KP_ATTR HS'); vm_compute; reflexivity
      | exact (kregs0_keep cx ms3 msn
                 (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity)) HR0)
      | unfold kregs_eq; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          first [ exact R22
                | lazymatch goal with |- getr (ms_regs _) (Z_to_bv 5 (Z.of_nat ?r)) = w64 _ =>
                    rewrite (HKP msn ssx HS' ltac:(vm_compute; reflexivity) r ltac:(kn_in));
                    apply (kn_reg_of ms3 _ r _ HRL); kn_in end ]
      | exact (proj1 (wvb_fds_fs _ _ _))
      | exact (proj2 (wvb_fds_fs _ _ _)) ]
    end.
Qed.

End b.
End a.
