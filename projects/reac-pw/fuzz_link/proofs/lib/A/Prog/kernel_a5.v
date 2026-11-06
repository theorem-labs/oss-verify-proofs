(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its addresses and numbers changed; 693 of its 921 lines of code are new or changed and 258 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the attribute case a % 6 = 5
   (lib/A/Prog/kernel_defs.v kin_acase at KP_A5, +0xc24) to the attribute loop's latch (kin_alat, +0xb44). Listing
   (internal path) (internal record, sha256 7bc02d6772b3), +0xc24 .. +0xf84.

   THE CODE. Three puts into w2 at w2 + n (n = w2.n): the 2-byte field (8, 0), the 2-byte field (0x63, 0), the
   4 bytes "abcd". Each is behind a room test `bltu (2^64 - 4098), n + L - 4097` (taken when n + L <= 4096); not
   taken, it stores w2.full := 1 and goes on to the next test. Then nl_pad (+0xf34): a1 = (n + 3) & 0xfffffffc, a
   test `bltu a1, 4097` (always taken: n <= 4096), s3 = a1 - n, and when a1 <> n checked_memset(w2 + n, 0, s3)
   (+0xf70); n += s3; s3 := slot 0xb0 (= a0 + 8); j +0xb44.

   A PRIVATE CUT at +0xf34 (nl_pad's start): a5_pad = kattr at pc 0xf34 with the loop's registers (s3 = a0 + 8 is
   not written by the puts). Two phases:
   (A) a5_put: +0xc24 -> +0xf34. kernel_k3.v's state (registers sr_atoms but s9 = w2 + 4096; atoms 32 = n,
   33 = full, 34 = w2 + n, 35 = k; the spill slots k3_sp, w2's two fields and the put bytes as regions; the alias
   w2 + n = atom 34), with pc +0xc24. The room tests wrap: the taken ones are in the facts' conditions (k3_conds,
   by k3_cond_ok); the not-taken ones the engine decides from n's range. The groups (n at the cut; pl the bytes
   put; the taken room tests' offsets c of `n + c`):
     n <= 4088: pl 8, all three | 4089..4092: 4, two | 4093..4094: 2, one | 4095..4096: 0, none.
   Each group is ONE run (LinkWalk paj_run_to_x) to +0xf34: w2.n = n + pl, w2.full = full (pl = 8) or 1.
   (B) a5_padl: +0xf34 -> +0xb44. The state: registers as in (A), atoms 32 = n, 33 = full, 34 = w2 + n; the slots
   0x98 (the mask), 0xa8 (4097), 0xb0 (a0 + 8), 0xc8, 0xd0, 0xd8 and w2's fields as regions. nl_pad's two tests are
   on `(n + 3) & 0xfffffffc`, which the engine does not simplify: both are in the facts' conditions (a5_pconds:
   the `bltu` taken; the `beq` taken when n is a multiple of 4, not taken else), each true by a5_pc_*. A multiple
   of 4 is ONE run to +0xb44; else a run to the call, the call (a5_call_ms: link_ajkit.v aj_gx_intrin_at over
   AMEMSET, w2 in kernel's own side frame F, shadow kfsh _ 0 _), and a run after it to +0xb44. At the end
   w2.n = (n + 3) & ~3.

   THE CUTS RE-ESTABLISHED. The runs and the call write only inside w2 (and the callee's window below s1), so
   kernel_kit.v kat_frame_w2 / kat_frame_w2s move every memory clause of the cut; kw_move gives w2's new fields.

   Section hypotheses used: LAWS (the run instances), LV (the callee's pc), AMEMSET (checked_memset).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
kernel_c kernel_defs kernel_kit kernel_next kernel_k3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition KP_PAD : Z := 0xf34.   (* nl_pad of case 5: `ld a0, 0(s9)` *)

(* ---- (A) the symbolic state at +0xc24: kernel_k3.v's at another pc ---- *)
Definition a5A_ss (lo hi pl : Z) (cs : list Z) : sstate :=
  mkSS (kpc KP_A5) k3_regs [k3_sp; k3_fl; k3_pr pl] None (k3_facts lo hi cs).

(* ---- (B) the symbolic state at +0xf34 ---- *)
Definition a5_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x98 0xe0 0 0
    [YP09.mkChunk 0x98 (CVal 8 (SLit 0xfffffffc)); YP09.mkChunk 0xa8 (CVal 8 (SLit 4097));
     YP09.mkChunk 0xb0 (CVal 8 (SOff 18 8)); YP09.mkChunk 0xc8 (CVal 8 (SOff 21 4104));
     YP09.mkChunk 0xd0 (CVal 8 (SLit (2 ^ 64 - 4098))); YP09.mkChunk 0xd8 (CVal 8 (SLit (2 ^ 64 - 4093)))].
(* nl_pad's (n + pl + 3) & 0xfffffffc, at atom 32 = n: c = pl + 3 *)
Definition a5_and (c : Z) : sv := SAlu ALU_AND (SOff 32 c) (SLit 0xfffffffc).
Definition a5_pconds (pl : Z) (z : bool) : list acond :=
  [mkAC BC_LTU (a5_and (pl + 3)) (SLit 4097); mkAC (if z then BC_EQ else BC_NE) (a5_and (pl + 3)) (SOff 32 pl)].
Definition a5B_facts (z : bool) : facts :=
  mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (21%nat, mkAF 4096 (2 ^ 47 - 4113) 0);
           (32%nat, mkAF 0 4096 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 4096 (2 ^ 47 - 4113) 0)]
    (a5_pconds 0 z) [(SAlu ALU_ADD (SOff 21 0) (SOff 32 0), SOff 34 0)].
Definition a5B_ss (z : bool) : sstate := mkSS (kpc KP_PAD) k3_regs [a5_sp; k3_fl] None (a5B_facts z).

(* ---- nl_pad's arithmetic ---- *)
Lemma a5_land : forall x, 0 <= x < 4200 -> Z.land x 0xfffffffc = x / 4 * 4.
Proof.
  assert (H : forallb (fun i => Z.land (Z.of_nat i) 0xfffffffc =? Z.of_nat i / 4 * 4) (seq 0 4200) = true)
    by (vm_compute; reflexivity).
  intros x Hx. rewrite forallb_forall in H.
  specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.

Lemma a5_U_and : forall E n c, bv_unsigned (ew E 32) = n -> 0 <= n + c < 4200 ->
  U E (SAlu ALU_AND (SOff 32 c) (SLit 0xfffffffc)) = (n + c) / 4 * 4.
Proof.
  intros E n c Hn Hc. rewrite U_SAlu, U_SOff, U_SLit, Hn. cbn [zalu_raw].
  rewrite (zcanon_id (n + c)) by (unfold M64; lia).
  rewrite (zcanon_id 0xfffffffc) by (unfold M64; lia).
  rewrite a5_land by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* the length checked_memset gets: a2 = s3 + 0 = ((n' + 3) & ~3) - n' *)
Lemma a5_U_len : forall E n pl c, bv_unsigned (ew E 32) = n -> c = pl + 3 -> 0 <= n + pl <= 4096 ->
  U E (SAlu ALU_ADD (SAlu ALU_SUB (SAlu ALU_AND (SOff 32 c) (SLit 0xfffffffc)) (SOff 32 pl)) (SLit 0)) =
    (n + pl + 3) / 4 * 4 - (n + pl).
Proof.
  intros E n pl c Hn -> H. rewrite U_SAlu, U_SAlu, U_SLit, U_SOff, Hn.
  rewrite (a5_U_and E n (pl + 3) Hn) by lia.
  cbn [zalu_raw]. rewrite (zcanon_id (n + pl)) by (unfold M64; lia).
  rewrite (zcanon_id 0) by (unfold M64; lia).
  replace (n + (pl + 3)) with (n + pl + 3) by ring.
  rewrite (zcanon_id ((n + pl + 3) / 4 * 4 - (n + pl))) by (unfold M64; lia).
  rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.

(* w2.n at the end: n' + (((n' + 3) & ~3) - n') *)
Lemma a5_U_fin : forall E n pl c, bv_unsigned (ew E 32) = n -> c = pl + 3 -> 0 <= n + pl <= 4096 ->
  U E (SAlu ALU_ADD (SOff 32 pl) (SAlu ALU_SUB (SAlu ALU_AND (SOff 32 c) (SLit 0xfffffffc)) (SOff 32 pl))) =
    (n + pl + 3) / 4 * 4.
Proof.
  intros E n pl c Hn -> H. rewrite U_SAlu, U_SAlu, U_SOff, Hn.
  rewrite (a5_U_and E n (pl + 3) Hn) by lia.
  cbn [zalu_raw]. rewrite (zcanon_id (n + pl)) by (unfold M64; lia).
  replace (n + (pl + 3)) with (n + pl + 3) by ring.
  rewrite (zcanon_id ((n + pl + 3) / 4 * 4 - (n + pl))) by (unfold M64; lia).
  replace (n + pl + ((n + pl + 3) / 4 * 4 - (n + pl))) with ((n + pl + 3) / 4 * 4) by ring.
  apply zcanon_id. unfold M64. lia.
Qed.

Lemma a5_pc_ltu : forall E n pl, bv_unsigned (ew E 32) = n -> 0 <= n + pl <= 4096 ->
  acond_ok E (mkAC BC_LTU (a5_and (pl + 3)) (SLit 4097)).
Proof.
  intros E n pl Hn H. unfold acond_ok, a5_and. cbn [ac_c ac_a ac_b].
  rewrite branch_ltu_U, U_SLit. rewrite (a5_U_and E n (pl + 3) Hn) by lia.
  rewrite (zcanon_id 4097) by (unfold M64; lia). apply Z.ltb_lt. lia.
Qed.

Lemma a5_pc_eq : forall E n pl, bv_unsigned (ew E 32) = n -> 0 <= n + pl <= 4096 -> (n + pl) mod 4 = 0 ->
  acond_ok E (mkAC BC_EQ (a5_and (pl + 3)) (SOff 32 pl)).
Proof.
  intros E n pl Hn H Hm. unfold acond_ok, a5_and. cbn [ac_c ac_a ac_b].
  rewrite branch_eq_U, U_SOff, Hn. rewrite (a5_U_and E n (pl + 3) Hn) by lia.
  rewrite (zcanon_id (n + pl)) by (unfold M64; lia). apply Z.eqb_eq. lia.
Qed.

Lemma a5_pc_ne : forall E n pl, bv_unsigned (ew E 32) = n -> 0 <= n + pl <= 4096 -> (n + pl) mod 4 <> 0 ->
  acond_ok E (mkAC BC_NE (a5_and (pl + 3)) (SOff 32 pl)).
Proof.
  intros E n pl Hn H Hm. unfold acond_ok, a5_and. cbn [ac_c ac_a ac_b].
  rewrite branch_ne_U, U_SOff, Hn. rewrite (a5_U_and E n (pl + 3) Hn) by lia.
  rewrite (zcanon_id (n + pl)) by (unfold M64; lia). apply negb_true_iff, Z.eqb_neq. lia.
Qed.

Lemma a5_conds_ok : forall E n (z : bool), bv_unsigned (ew E 32) = n -> 0 <= n <= 4096 ->
  (if z then n mod 4 = 0 else n mod 4 <> 0) -> conds_ok E (a5_pconds 0 z).
Proof.
  intros E n z Hn H Hz. unfold a5_pconds. cbn [conds_ok].
  split; [exact (a5_pc_ltu E n 0 Hn ltac:(lia))|]. split; [|exact I].
  destruct z; [exact (a5_pc_eq E n 0 Hn ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hz))
             | exact (a5_pc_ne E n 0 Hn ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hz))].
Qed.

(* the windows of (B)'s state lie in w2 *)
Lemma a5B_windows : forall (E : env) z w,
  base_val E (Some 21%nat) = w ->
  forall b wlo whi a, In (b, wlo, whi) (windows (ss_mem (a5B_ss z))) ->
    base_val E b + wlo <= a < base_val E b + whi -> w <= a < w + NW_SIZE.
Proof.
  intros E z w H21 b wlo whi a Hin Ha.
  unfold a5B_ss, windows in Hin.
  cbn [ss_mem map In a5_sp k3_fl YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  unfold NW_SIZE.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-.
  - lia.
  - rewrite H21 in Ha. lia.
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
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.

(* the registers a run does not write: the same symbolic value at its start and at a call stop *)
Lemma a5_reg_same : forall E ss0 ss1 (H : word -> bool) (ms0 ms1 : machine_state) (l : list Z),
  st_ok_pi SEGS pa_val E ss0 (restrict H ms0) -> st_ok SEGS E ss1 (restrict H ms1) ->
  forallb (fun k => sv_eqb (sr_get (ss_regs ss1) (Z_to_bv 5 k)) (sr_get (ss_regs ss0) (Z_to_bv 5 k))) l = true ->
  forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) l = true -> getr (ms_regs ms1) r = getr (ms_regs ms0) r.
Proof.
  intros E ss0 ss1 H ms0 ms1 l HS0 HS1 Hl r Hr.
  apply existsb_exists in Hr as (k & Hk & Hrk). apply Z.eqb_eq in Hrk.
  rewrite forallb_forall in Hl. pose proof (Hl k Hk) as Hs. apply sv_eqb_eq in Hs.
  assert (Er : r = Z_to_bv 5 k) by (rewrite <- Hrk; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite (st_ok_restrict_reg SEGS H E ss1 ms1 r HS1), (st_ok_pi_restrict_reg H E ss0 ms0 r HS0), Er, Hs.
  reflexivity.
Qed.

(* ---- THE CALL: checked_memset(w2 + d, 0, L) from s1 (link_ajkit.v aj_gx_intrin_at), w2 in F whose shadow is
   kfsh _ 0 _; the run before it changed only w2 ---- *)
Lemma a5_call_ms : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md0 mm md (rg : bvmap 5 word) raw d L
    (Q : world SEGS -> config -> Prop),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md k2 ->
  kjbk B cx fpos k2 ly3 S3 md0 ->
  kshadow cx fpos W3 ms3 (kfsh 0xf8 0 0xf3) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) ->
     aview SEGS (w_H W3) mm a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  0 <= d -> 0 < L -> d + L <= NW_SIZE ->
  getr rg 10 = w64 (kW2 cx fpos + d) -> getr rg 11 = w64 0 -> getr rg 12 = w64 L -> getr rg 2 = w64 (ksp1 cx) ->
  getr rg 3 = getr (k_regs cx) 3 -> getr rg 4 = getr (k_regs cx) 4 -> getr rg 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2,
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
       (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mem2 md2 k2 ->
     aregs_preserved rg regs2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (kW2 cx fpos + d <= a < kW2 cx fpos + d + L) ->
        ~ (ksp1 cx - ESTACK <= a < ksp1 cx) -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mm a) ->
     (forall a, apresent (w_H W3) mm a -> apresent (w_H W3) mem2 a) ->
     same_but_materialized md md2 ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 0x53214) mm (seg_rom SEGS)) md) Q.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md0 mm md rg raw d L Q HB HJ HJB HSH0 UN1 Hd HL HdL R10 R11 R12 R2 R3 R4 R1 Hraw
    CONT.
  pose proof HB as (HPRE & _). pose proof HPRE as (HJ0 & HGok & _ & _ & _ & Hgp & Htp & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md0 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  rewrite Hfb in F2, F3.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  assert (Hsp : spZ rg = ksp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  assert (HFS : kFSH cx fpos = SHADOW_OFF + kF cx fpos / 8) by reflexivity.
  (* F's shadow at the call's memory *)
  assert (HSH : kshadow cx fpos W3 (mkst rg (Z_to_bv 64 0x53214) mm (seg_rom SEGS)) (kfsh 0xf8 0 0xf3)).
  { apply (kshadow_frame B LAWS (fun a => kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) cx fpos _ k2 ly3 S3 md0 W3 ms3
             W3 _ HJB); [| rewrite kfsh_length; lia | | exact HSH0].
    - intros a Ha Hn. cbn [ms_mem mkst]. exact (UN1 a Ha Hn).
    - intros a Ha Hw. rewrite kfsh_length in Ha. unfold kW2, KN_W2, NW_SIZE in Hw.
      unfold SHADOW_OFF in HFS. lia. }
  pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md0 W3 _ 0xf8 0xf3 HJB HSH) as HRA.
  cbn [ms_mem mkst] in HRA.
  (* F, at the current layout *)
  pose proof HPRE as (HJ0' & _).
  assert (HFA : frame_addr ly3 KN_CID fpos = kF cx fpos).
  { destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos HJ)
      as (HA1 & _).
    destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos HJ0')
      as (HA2 & _).
    unfold kF. now rewrite HA1, HA2. }
  (* the shadow address of a byte of w2 *)
  assert (HSA : forall x, kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE ->
            kFSH cx fpos + 0x226 <= shadow_addr x <= kFSH cx fpos + 0x427).
  { intros x Hx. rewrite HFS. unfold shadow_addr. unfold kW2, KN_W2, NW_SIZE in Hx. lia. }
  eapply SRr_bind.
  - eapply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet 0x53214 AMEMSET (k_G cx) (k_XO cx) (k_OUT cx) W3 rg
      mm (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) _ ly3 S3 md k2
      (kW2 cx fpos + d) 0 L raw HGok HJ R10 R11 R12);
    [ unfold NW_SIZE in HdL; lia | unfold kW2, KN_W2; lia | unfold kW2, KN_W2, NW_SIZE in *; lia
    | rewrite Hsp; lia | rewrite Hsp, HES; rewrite HK8 in S6; lia | rewrite Hsp; lia
    | rewrite R3; exact Hgp | rewrite R4; exact Htp | exact R1 | exact Hraw
    | | | | | exact I ].
    + intros a Ha. left. split; [|split].
      * apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos a HJ).
        -- left. reflexivity.
        -- left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFA, Hfb.
           unfold kW2, KN_W2, NW_SIZE in *. lia.
      * unfold kW2, KN_W2, NW_SIZE in *. lia.
      * rewrite Hsp, HES. rewrite HK8 in S6. unfold kW2, KN_W2, NW_SIZE in *. lia.
    + unfold amem_range, kLowMemEnd, kHighMemEnd, kW2, KN_W2, NW_SIZE in *. unfold kHighMemBeg in *. lia.
    + intros x Hx. apply HRA. lia.
    + intros _ s Hs.
      pose proof (HSA (kW2 cx fpos + d) ltac:(lia)) as Q1.
      pose proof (HSA (kW2 cx fpos + d + L - 1) ltac:(lia)) as Q2.
      assert (HF8 : kFSH cx fpos mod 8 = 0) by (rewrite HFS; unfold SHADOW_OFF; lia).
      assert (Hi : 0x220 <= s - kFSH cx fpos < 0x428) by lia.
      unfold kshadow in HSH. cbn [ms_mem mkst] in HSH.
      replace s with (kFSH cx fpos + Z.of_nat (Z.to_nat (s - kFSH cx fpos))) by (rewrite Z2Nat.id; lia).
      rewrite (HSH (Z.to_nat (s - kFSH cx fpos))) by (rewrite kfsh_length; lia). discriminate.
  - cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & _ & Hfr & Hpres & Hsbm).
    apply (CONT regs2 mem2 md2 HJ2 HP2); [| exact Hpres | exact Hsbm].
    intros a Ha Hd' Hw. apply Hfr; [exact Ha | exact Hd' | rewrite Hsp; exact Hw].
Qed.

(* the private cut at +0xf34: the attribute loop's state *)
Definition a5_pad (Rc Rm Ra : kcx -> Z -> Prop) := kattr B Rc Rm Ra KP_PAD [] (fun _ _ => True).

(* w2 lies in F: every byte is a writable byte of the journal, outside the out cells *)
Lemma a5_awf : forall cx fpos k2 ly3 S3 W3 mm md,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md k2 ->
  forall x, kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE ->
    awr_byte (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3
      ((KN_CID, fpos) :: k_own cx) x /\ ~ (k_sp0 cx <= x < k_sp0 cx + k_XO cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 mm md HB HJ x Hx.
  pose proof HB as (HPRE & _). pose proof HPRE as (HJ0 & _).
  assert (HFA : frame_addr ly3 KN_CID fpos = kF cx fpos).
  { destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos HJ)
      as (HA1 & _).
    destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos HJ0)
      as (HA2 & _).
    unfold kF. now rewrite HA1, HA2. }
  apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos x HJ).
  - left. reflexivity.
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFA, kn_fsb8. unfold kW2, KN_W2, NW_SIZE in Hx. lia.
Qed.

(* ---- (A) THE START: kernel_k3.v's state, shadow entries and writable windows, at +0xc24 ---- *)
Lemma a5A_start : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 c ci j m k n f adv hd kd left a p (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_A5
    ((19%nat, ka0 cx + 8) :: (21%nat, kW2 cx fpos) :: (24%nat, kS8 cx) :: (25%nat, kW2 cx fpos + NW_N) ::
     (22%nat, left) :: [(23%nat, a); (27%nat, p)])
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  0 <= k < 5 ->
  E = Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos n f k)) ->
  forall lo hi pl cs,
  lo <= n <= hi -> 0 <= pl -> n + pl <= 4096 ->
  regions_wf [k3_sp; k3_fl; k3_pr pl] = true ->
  Forall (fun c => -4098 < n + c < 0) cs ->
  st_ok_pi SEGS pa_val E (a5A_ss lo hi pl cs) (restrict (w_H W3) ms3) /\
  sh_ok SEGS k3_Bx (k3_SH pl) E (mrestrict (w_H W3) (ms_mem ms3)) /\
  awr_ok_x E (ss_mem (a5A_ss lo hi pl cs)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd left a p E HB HJ HW HAT Hk HEdef lo hi pl cs Hn
    Hpl Hnpl Hwf Hcs.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  pose proof (kn_reg_of ms3 _ 25 (kW2 cx fpos + NW_N) HRL ltac:(kn_in)) as R25.
  pose proof HW as (Hw0 & Hwl & Hpres & Hnv & Hfv & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 n f k E HB HJB HR0 R21 ltac:(lia) Hfr Hk HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _ & HFsh).
  pose proof kn_band as (KB1 & KB2).
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  pose proof (kn_sp SK B cx HB) as (Hac & _ & _ & Hs1 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & _ & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact B9.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV34 : base_val E (Some 34%nat) = kW2 cx fpos + n) by exact B34.
  pose proof (kn_slot_of cx W3 ms3 _ KS_K k HSL ltac:(apply in_or_app; right; kn_in)) as SL_K.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W2F (kW2 cx fpos + NW_FULL) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_W2F.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4098 (2 ^ 64 - 4098) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_M4098.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4093 (2 ^ 64 - 4093) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_M4093.
  pose proof (a5_awf cx fpos k2 ly3 S3 W3 _ _ HB HJ) as AWF.
  pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HRA.
  split; [|split].
  - (* the symbolic state *)
    rewrite (kn_ms_shape ms3 (BASE + kpc KP_A5) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold a5A_ss. apply pa_entry_st_ok_full.
    + unfold k3_regs.
      apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R25. cbn [sv_denot]. rewrite B21. reflexivity.
    + exact Hwf.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * unfold k3_sp, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xa0 (SOff 35 0) k); [|exact SL_K].
           cbn [sv_denot]. rewrite B35, Z.add_0_r. reflexivity.
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc8 (SOff 21 4104) (kW2 cx fpos + NW_FULL));
             [|exact SL_W2F].
           cbn [sv_denot]. rewrite B21. reflexivity.
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xd0 (SLit (2 ^ 64 - 4098)) (2 ^ 64 - 4098));
             [reflexivity | exact SL_M4098].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xd8 (SLit (2 ^ 64 - 4093)) (2 ^ 64 - 4093));
             [reflexivity | exact SL_M4093].
      * unfold k3_fl, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV21.
        split; [lia|]. split; [unfold NW_SIZE in Hwl; lia|]. split.
        { intros o Ho. exact (proj2 (Hpres o ltac:(unfold NW_SIZE; lia))). }
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS E _ (kW2 cx fpos) 4096 8 (SOff 32 0) n).
           ++ cbn [sv_denot]. rewrite B32, Z.add_0_r. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
           ++ change (Z.of_N 8) with 8. lia.
           ++ exact Hnv.
        -- apply (chunk_ok_val SEGS E _ (kW2 cx fpos) 4104 4 (SOff 33 0) f).
           ++ cbn [sv_denot]. rewrite B33, Z.add_0_r. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
           ++ change (Z.of_N 4) with 4. lia.
           ++ exact Hfv.
      * unfold k3_pr, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV34.
        split; [lia|]. split; [unfold NW_SIZE in Hwl; lia|]. split; [|apply Forall_nil].
        intros o Ho. replace (kW2 cx fpos + n + o) with (kW2 cx fpos + (n + o)) by lia.
        exact (proj2 (Hpres (n + o) ltac:(unfold NW_SIZE; lia))).
    + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, k3_sp, k3_fl, k3_pr.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV9, BV21, BV34. rewrite HKA in Hac.
      repeat split; lia.
    + unfold k3_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok alias_ok].
      split; [|split].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B20, B21, B32, B33, B34.
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
        refine (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _))
          (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _)) I))))); lia.
      * exact (k3_conds_ok E n cs B32 Hcs).
      * split; [|exact I].
        rewrite (denot_lit_U E (SAlu ALU_ADD (SOff 21 0) (SOff 32 0))), (denot_lit_U E (SOff 34 0)). f_equal.
        rewrite U_SAlu, !U_SOff. cbn [zalu_raw].
        rewrite B21, B32, B34, !Z.add_0_r.
        rewrite (zcanon_id (kW2 cx fpos)), (zcanon_id n) by (unfold M64; lia). reflexivity.
  - (* the shadow entries *)
    assert (HUB : U E k3_Bx = SHADOW_OFF)
      by (unfold k3_Bx; apply k3_U0; [exact B20 | unfold SHADOW_OFF; lia]).
    unfold sh_ok, k3_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E k3_Bx 21 (kW2 cx fpos) NW_SIZE (kW2 cx fpos)
               4096 4112 HRA HUB); [apply k3_U0; [exact B21 | lia] | lia | unfold NW_SIZE; lia |].
      intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
    + apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E k3_Bx 34 (kW2 cx fpos) NW_SIZE (kW2 cx fpos + n)
               0 (pl + 8) HRA HUB); [apply k3_U0; [exact B34 | lia] | lia | unfold NW_SIZE; lia |].
      intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
  - (* the writable windows lie in F *)
    unfold a5A_ss. cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; unfold k3_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    + intros x Hx. unfold k3_fl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV21 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
    + intros x Hx. unfold k3_pr in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV34 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
Qed.

(* ---- (A) THE END: the cut at +0xf34, from the run's end state ---- *)
Lemma a5A_end : forall POST (Rc Rm Ra : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv hd kd left a p (E : env),
  kfrom SK B POST (a5_pad Rc Rm Ra) ->
  kbase SK B cx ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> Ra cx left ->
  1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m -> (kd = 0 \/ kd = 7) ->
  1 <= left <= 4 -> 0 <= hd <= n ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_A5
    ((19%nat, ka0 cx + 8) :: (21%nat, kW2 cx fpos) :: (24%nat, kS8 cx) :: (25%nat, kW2 cx fpos + NW_N) ::
     (22%nat, left) :: [(23%nat, a); (27%nat, p)])
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  bv_unsigned (ew E 21) = kW2 cx fpos -> bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 33) = f ->
  bv_unsigned (ew E 34) = kW2 cx fpos + n ->
  forall lo hi pl cs, 0 <= pl -> n + pl <= 4096 ->
  forall (ms : machine_state) md cs' fe f',
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs') ->
  frame_of E (ss_mem (a5A_ss lo hi pl cs)) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  kms KP_PAD ms ->
  (forall r, In r nx_keep0 -> getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  (forall r, In r (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 22]%nat) ->
     getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 25)) = sv_denot E (SOff 21 4096) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  In (YP09.mkChunk 4096 (CVal 8 (SOff 32 pl))) cs' ->
  In (YP09.mkChunk 4104 (CVal 4 fe)) cs' ->
  (fe = SOff 33 0 /\ f' = f) \/ (fe = SLit 1 /\ f' = 1) ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd left a p E HN HB HFR HRc HRm HRa
    Hc Hci Hj Hm Hk Hkd Hl Hhd HW HAT B21 B32 B33 B34 lo hi pl cs Hpl Hnpl ms md cs' fe f' HR1 HFr HG HJ HMS HK0
    HKN H25 Hfds Hfs Hin1 Hin2 Hfe.
  pose proof HAT as (_ & HR0 & HRL & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV34 : base_val E (Some 34%nat) = kW2 cx fpos + n) by exact B34.
  assert (Hf' : 0 <= f' <= 1) by (destruct Hfe as [(_ & ->) | (_ & ->)]; lia).
  assert (HP : forall q, apresent (w_H W3) (ms_mem ms3) q -> apresent (w_H W3) (ms_mem ms) q)
    by (intros q Hq; exact (k3_apres_grows _ _ _ q HG Hq)).
  assert (HK : forall r : nat, In r [19; 21; 24; 22]%nat ->
            getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
    by (intros r Hr; exact (HKN _ (kn_in_map5 r _ Hr))).
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  exists c, ci, j, m, k, (n + pl), f', adv, hd, kd, left.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact HRa|]. split; [exact Hc|]. split; [exact Hci|].
  split; [exact Hj|]. split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|]. split; [exact Hl|].
  split; [lia|].
  split.
  { apply (kw_move W3 ms3 W3 ms (kW2 cx fpos) n f (n + pl) f' HW HP).
    - exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4096 8 (SOff 32 pl) (n + pl) HR1 B21 Hin1
               ltac:(cbn [sv_denot]; rewrite B32; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
    - destruct Hfe as [(-> & ->) | (-> & ->)].
      + exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SOff 33 0) f HR1 B21 Hin2
                 ltac:(cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
      + exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SLit 1) 1 HR1 B21 Hin2
                 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
    - unfold NL_CHUNK_MAX. lia.
    - exact Hf'. }
  split; [exact I|].
  apply (kat_frame_w2 SK B LAWS 0 NW_SIZE cx fpos KP_A5 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 KP_PAD _ _
           W3 ms md HB HAT HMS (kregs0_keep cx ms3 ms HK0 HR0)).
  - unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    + rewrite (HK 19%nat) by kn_in. apply (kn_reg_of ms3 _ 19 (ka0 cx + 8) HRL). kn_in.
    + rewrite (HK 21%nat) by kn_in. apply (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL). kn_in.
    + rewrite (HK 24%nat) by kn_in. apply (kn_reg_of ms3 _ 24 (kS8 cx) HRL). kn_in.
    + rewrite H25. cbn [sv_denot]. rewrite B21. reflexivity.
    + rewrite (HK 22%nat) by kn_in. apply (kn_reg_of ms3 _ 22 left HRL). kn_in.
  - intros x Hx. exact Hx.
  - reflexivity.
  - apply kfsh_fits.
  - exact Hfds.
  - exact Hfs.
  - lia.
  - lia.
  - intros q Hq Hnq.
    apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms)
             (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr); [|exact Hq | intros Hc'; apply Hnq; lia].
    exact (k3_windows E lo hi pl cs (kW2 cx fpos) n BV21 BV34 ltac:(lia) Hpl Hnpl).
  - exact HP.
Qed.

(* ---- (A) the run of one group, from +0xc24 to +0xf34 (KST: a5A_start at the cut, KFIN: a5A_end at it) ---- *)
Ltac a5A_go KST KFIN RUNTO HJ HAG lo hi pl cs fv fe :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAWR := fresh "HAWR" in
  destruct (KST lo hi pl cs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              ltac:(repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil)) as (HS & SHOK & HAWR);
  paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_PAD); [exact HAWR|];
  lazymatch goal with
  | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
    HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
    HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    let HR1 := fresh "HR1" in
    spregion HS' 1%nat HR1;
    apply (KFIN lo hi pl cs ltac:(lia) ltac:(lia) msn mdn _ fe fv HR1 HFr' HG');
    [ assumption
    | apply (kn_kms_of _ E ssx msn KP_PAD HS'); vm_compute; reflexivity
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 22]%nat)
               HS' HAG ltac:(vm_compute; reflexivity))
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | exact (proj1 (wvb_fds_fs _ _ _))
    | exact (proj2 (wvb_fds_fs _ _ _))
    | kn_in
    | kn_in
    | first [left; split; reflexivity | right; split; reflexivity] ]
  end.

(* ---- (A) THE PHASE: the puts ---- *)
Theorem a5_put : forall POST (Rc Rm Ra : kcx -> Z -> Prop),
  kfrom SK B POST (a5_pad Rc Rm Ra) -> kfrom SK B POST (kin_acase B Rc Rm Ra KP_A5 ka_5).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qa & qp & _ & _ & _ & HK).
  destruct HK as (qc & qci & qj & qm & qk & qn & qf & qadv & qhd & qkd & ql & HRc & HRm & HRa & Hc & Hci & Hj & Hm & Hk
    & Hkd & Hl & Hhd & HW & _ & HAT).
  pose proof HAT as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  remember (Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk))) as Eq3 eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM Eq3) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk)) Eq3)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 qn qf qk Eq3 HB HJB HR0 R21 ltac:(lia) Hfr ltac:(lia) HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  pose proof (a5A_start cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd ql qa qp Eq3 HB HJ HW HAT
                ltac:(lia) HEdef) as KST.
  pose proof (a5A_end POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd ql qa qp Eq3 HN
                HB HFR HRc HRm HRa Hc Hci Hj Hm Hk Hkd Hl Hhd HW HAT B21 B32 B33 B34) as KFIN.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  destruct (Z_le_gt_dec qn 4088) as [G|G];
    [a5A_go KST KFIN RUNTO HJ HAG 0 4088 8 ([-4095; -4093; -4089]) qf (SOff 33 0)|].
  destruct (Z_le_gt_dec qn 4092) as [G'|G'];
    [a5A_go KST KFIN RUNTO HJ HAG 4089 4092 4 ([-4095; -4093]) 1 (SLit 1)|].
  destruct (Z_le_gt_dec qn 4094) as [G''|G''];
    [a5A_go KST KFIN RUNTO HJ HAG 4093 4094 2 ([-4095]) 1 (SLit 1)|].
  a5A_go KST KFIN RUNTO HJ HAG 4095 4096 0 (@nil Z) 1 (SLit 1).
Qed.

(* ---- (B) THE START: the symbolic state and its writable windows at +0xf34 ---- *)
Lemma a5B_start : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 c ci j m k n f adv hd kd left (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_PAD
    ((19%nat, ka0 cx + 8) :: (21%nat, kW2 cx fpos) :: (24%nat, kS8 cx) :: (25%nat, kW2 cx fpos + NW_N) ::
     (22%nat, left) :: [])
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  0 <= k < 5 ->
  E = Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos n f k)) ->
  bv_unsigned (ew E 18) = ka0 cx ->
  forall z : bool, (if z then n mod 4 = 0 else n mod 4 <> 0) ->
  st_ok_pi SEGS pa_val E (a5B_ss z) (restrict (w_H W3) ms3) /\
  awr_ok_x E (ss_mem (a5B_ss z)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd left E HB HJ HW HAT Hk HEdef E18 z Hz.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  pose proof (kn_reg_of ms3 _ 25 (kW2 cx fpos + NW_N) HRL ltac:(kn_in)) as R25.
  pose proof HW as (Hw0 & Hwl & Hpres & Hnv & Hfv & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 n f k E HB HJB HR0 R21 ltac:(lia) Hfr Hk HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof (kn_sp SK B cx HB) as (Hac & _ & _ & Hs1 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & _ & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact B9.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  pose proof (kn_slot_of cx W3 ms3 _ KS_MASK 0xfffffffc HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_MASK.
  pose proof (kn_slot_of cx W3 ms3 _ KS_ROOM 4097 HSL ltac:(apply in_or_app; right; kn_in)) as SL_ROOM.
  pose proof (kn_slot_of cx W3 ms3 _ KS_CN (ka0 cx + 8) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_CN.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W2F (kW2 cx fpos + NW_FULL) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_W2F.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4098 (2 ^ 64 - 4098) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_M4098.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4093 (2 ^ 64 - 4093) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_M4093.
  pose proof (a5_awf cx fpos k2 ly3 S3 W3 _ _ HB HJ) as AWF.
  split.
  - (* the symbolic state *)
    rewrite (kn_ms_shape ms3 (BASE + kpc KP_PAD) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold a5B_ss. apply pa_entry_st_ok_full.
    + unfold k3_regs.
      apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R25. cbn [sv_denot]. rewrite B21. reflexivity.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold a5_sp, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; [..|apply Forall_nil].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x98 (SLit 0xfffffffc) 0xfffffffc);
             [reflexivity | exact SL_MASK].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xa8 (SLit 4097) 4097);
             [reflexivity | exact SL_ROOM].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb0 (SOff 18 8) (ka0 cx + 8)); [|exact SL_CN].
           cbn [sv_denot]. rewrite E18. reflexivity.
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc8 (SOff 21 4104) (kW2 cx fpos + NW_FULL));
             [|exact SL_W2F].
           cbn [sv_denot]. rewrite B21. reflexivity.
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xd0 (SLit (2 ^ 64 - 4098)) (2 ^ 64 - 4098));
             [reflexivity | exact SL_M4098].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xd8 (SLit (2 ^ 64 - 4093)) (2 ^ 64 - 4093));
             [reflexivity | exact SL_M4093].
      * unfold k3_fl, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV21.
        split; [lia|]. split; [unfold NW_SIZE in Hwl; lia|]. split.
        { intros o Ho. exact (proj2 (Hpres o ltac:(unfold NW_SIZE; lia))). }
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS E _ (kW2 cx fpos) 4096 8 (SOff 32 0) n).
           ++ cbn [sv_denot]. rewrite B32, Z.add_0_r. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
           ++ change (Z.of_N 8) with 8. lia.
           ++ exact Hnv.
        -- apply (chunk_ok_val SEGS E _ (kW2 cx fpos) 4104 4 (SOff 33 0) f).
           ++ cbn [sv_denot]. rewrite B33, Z.add_0_r. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
           ++ change (Z.of_N 4) with 4. lia.
           ++ exact Hfv.
    + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, a5_sp, k3_fl.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV9, BV21. rewrite HKA in Hac.
      repeat split; lia.
    + unfold a5B_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok alias_ok].
      split; [|split].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B20, B21, B32, B33, B34.
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
        refine (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _))
          (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _)) I))))); lia.
      * exact (a5_conds_ok E n z B32 ltac:(lia) Hz).
      * split; [|exact I].
        rewrite (denot_lit_U E (SAlu ALU_ADD (SOff 21 0) (SOff 32 0))), (denot_lit_U E (SOff 34 0)). f_equal.
        rewrite U_SAlu, !U_SOff. cbn [zalu_raw].
        rewrite B21, B32, B34, !Z.add_0_r.
        rewrite (zcanon_id (kW2 cx fpos)), (zcanon_id n) by (unfold M64; lia). reflexivity.
  - (* the writable windows lie in F *)
    unfold a5B_ss. cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; unfold a5_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold k3_fl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV21 in Hx.
    left. apply AWF. unfold NW_SIZE. lia.
Qed.

(* ---- (B) THE END: the latch cut, from the end state's field region, frame and registers ---- *)
Lemma a5B_end : forall POST (Rc Rm Ra : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv hd kd left,
  kfrom SK B POST (kin_alat B Rc Rm Ra) ->
  kbase SK B cx ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> Ra cx left ->
  1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m -> (kd = 0 \/ kd = 7) ->
  1 <= left <= 4 -> 0 <= hd <= n ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_PAD
    ((19%nat, ka0 cx + 8) :: (21%nat, kW2 cx fpos) :: (24%nat, kS8 cx) :: (25%nat, kW2 cx fpos + NW_N) ::
     (22%nat, left) :: [])
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  forall (E : env) (ms : machine_state) md cs',
  bv_unsigned (ew E 21) = kW2 cx fpos -> bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 33) = f ->
  bv_unsigned (ew E 18) = ka0 cx ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= a < ksp1 cx)) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms) a) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  kms KP_ALAT ms ->
  (forall r, In r nx_keep0 -> getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  (forall r, In r (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24; 22]%nat) ->
     getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 25)) = sv_denot E (SOff 21 4096) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 19)) = sv_denot E (SOff 18 8) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  In (YP09.mkChunk 4096
        (CVal 8 (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SUB (SAlu ALU_AND (SOff 32 3) (SLit 0xfffffffc)) (SOff 32 0)))))
     cs' ->
  In (YP09.mkChunk 4104 (CVal 4 (SOff 33 0))) cs' ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd left HN HB HFR HRc HRm HRa Hc Hci Hj
    Hm Hk Hkd Hl Hhd HW HAT E ms md cs' B21 B32 B33 B18 HR1 UN HP HJ HMS HK0 HKN H25 H19 Hfds Hfs Hin1 Hin2.
  pose proof HAT as (_ & HR0 & HRL & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HK : forall r : nat, In r [21; 24; 22]%nat ->
            getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
    by (intros r Hr; exact (HKN _ (kn_in_map5 r _ Hr))).
  assert (Hn' : U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SUB (SAlu ALU_AND (SOff 32 3) (SLit 0xfffffffc)) (SOff 32 0)))
                = (n + 0 + 3) / 4 * 4) by exact (a5_U_fin E n 0 3 B32 eq_refl ltac:(lia)).
  rewrite Z.add_0_r in Hn'.
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  exists c, ci, j, m, k, ((n + 3) / 4 * 4), f, adv, hd, kd, left.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact HRa|]. split; [exact Hc|]. split; [exact Hci|].
  split; [exact Hj|]. split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|]. split; [exact Hl|].
  split; [lia|].
  split.
  { apply (kw_move W3 ms3 W3 ms (kW2 cx fpos) n f ((n + 3) / 4 * 4) f HW HP).
    - refine (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4096 8 _ ((n + 3) / 4 * 4) HR1 B21 Hin1 _
               ltac:(cbn; lia) ltac:(cbn; lia)).
      rewrite denot_lit_U, Hn'. reflexivity.
    - exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SOff 33 0) f HR1 B21 Hin2
               ltac:(cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
    - unfold NL_CHUNK_MAX. lia.
    - exact Hfr. }
  split; [exact I|].
  apply (kat_frame_w2s SK B LAWS 0 NW_SIZE cx fpos KP_PAD _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 KP_ALAT _ _
           W3 ms md HB HAT HMS (kregs0_keep cx ms3 ms HK0 HR0)).
  - unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    + rewrite H19. cbn [sv_denot]. rewrite B18. reflexivity.
    + rewrite (HK 21%nat) by kn_in. apply (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL). kn_in.
    + rewrite (HK 24%nat) by kn_in. apply (kn_reg_of ms3 _ 24 (kS8 cx) HRL). kn_in.
    + rewrite H25. cbn [sv_denot]. rewrite B21. reflexivity.
    + rewrite (HK 22%nat) by kn_in. apply (kn_reg_of ms3 _ 22 left HRL). kn_in.
  - intros x Hx. exact Hx.
  - reflexivity.
  - apply kfsh_fits.
  - exact Hfds.
  - exact Hfs.
  - lia.
  - lia.
  - intros q Hq Hnq. apply UN; [exact Hq|]. intros [Hc'|Hc']; apply Hnq; [left; lia | right; exact Hc'].
  - exact HP.
Qed.

(* w2 stays addressable while only w2 and the callee's window change *)
Lemma a5_w2_ra : forall cx fpos k2 ly3 S3 md3 W3 (ms3 : machine_state) mm,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kshadow cx fpos W3 ms3 (kfsh 0xf8 0 0xf3) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= a < ksp1 cx)) ->
     aview SEGS (w_H W3) mm a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  range_addressable (aview SEGS (w_H W3) mm) SHADOW_OFF (kW2 cx fpos) NW_SIZE.
Proof.
  intros cx fpos k2 ly3 S3 md3 W3 ms3 mm HB HJB HSH UN.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _ & HFsh).
  pose proof kn_band as (KB1 & KB2).
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (HSH' : kshadow cx fpos W3 (mkst (ms_regs ms3) (ms_pc_val ms3) mm (ms_rom ms3)) (kfsh 0xf8 0 0xf3)).
  { apply (kshadow_frame B LAWS
             (fun a => (kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= a < ksp1 cx))
             cx fpos _ k2 ly3 S3 md3 W3 ms3 W3 _ HJB); [| rewrite kfsh_length; lia | | exact HSH].
    - intros a Ha Hn. cbn [ms_mem mkst]. exact (UN a Ha Hn).
    - intros a Ha Hw. rewrite kfsh_length in Ha.
      unfold kFSH, shadow_of_addr, kW2, KN_W2, NW_SIZE, SHADOW_OFF in *. lia. }
  pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 _ 0xf8 0xf3 HJB HSH') as HRA.
  cbn [ms_mem mkst] in HRA. exact HRA.
Qed.

(* the shadow entry of w2's fields *)
Lemma a5_shok_fl : forall cx fpos k2 ly3 S3 md3 (W3 : world SEGS) mm (E : env),
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  range_addressable (aview SEGS (w_H W3) mm) SHADOW_OFF (kW2 cx fpos) NW_SIZE ->
  bv_unsigned (ew E 20) = SHADOW_OFF -> bv_unsigned (ew E 21) = kW2 cx fpos ->
  sh_ok SEGS k3_Bx [mkSHE 21 4096 4112] E (mrestrict (w_H W3) mm).
Proof.
  intros cx fpos k2 ly3 S3 md3 W3 mm E HB HJB HRA B20 B21.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _ & HFsh).
  pose proof kn_band as (KB1 & KB2).
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (HUB : U E k3_Bx = SHADOW_OFF)
    by (unfold k3_Bx; apply k3_U0; [exact B20 | unfold SHADOW_OFF; lia]).
  unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W3) mm E k3_Bx 21 (kW2 cx fpos) NW_SIZE (kW2 cx fpos)
           4096 4112 HRA HUB); [apply k3_U0; [exact B21 | lia] | lia | unfold NW_SIZE; lia |].
  intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
Qed.

(* (B)'s models: a run materializes the lazy backing; a call keeps descriptors and files *)
Ltac a5_md := first [ exact (proj1 (wvb_fds_fs _ _ _)) | exact (proj2 (wvb_fds_fs _ _ _)) | reflexivity ].

(* ---- (B) THE PHASE: nl_pad ---- *)
Theorem a5_padl : forall POST (Rc Rm Ra : kcx -> Z -> Prop),
  kfrom SK B POST (kin_alat B Rc Rm Ra) -> kfrom SK B POST (a5_pad Rc Rm Ra).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qc & qci & qj & qm & qk & qn & qf & qadv & qhd & qkd & ql & HRc & HRm & HRa & Hc & Hci & Hj & Hm & Hk
    & Hkd & Hl & Hhd & HW & _ & HAT).
  pose proof HAT as (_ & HR0 & HRL & _ & HFRM & HSH & _ & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  remember (Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk))) as Eq3 eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM Eq3) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk)) Eq3)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 qn qf qk Eq3 HB HJB HR0 R21 ltac:(lia) Hfr ltac:(lia) HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  assert (Hka : 0 <= ka0 cx < 2 ^ 47)
    by (destruct (kn_ard_bound SK B LAWS cx (ka0 cx) HB (kn_ard_cur cx (ka0 cx) ltac:(lia))) as (Hq & _); lia).
  assert (B18 : bv_unsigned (ew Eq3 18) = ka0 cx).
  { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 18 18%bv eq_refl).
    destruct HR0 as (_ & _ & _ & _ & _ & R18 & _). rewrite R18. unfold w64. apply unsigned_lit_small. lia. }
  assert (BV21 : base_val Eq3 (Some 21%nat) = kW2 cx fpos) by exact B21.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof (kn_sp SK B cx HB) as (Hac & Hsp2 & _ & Hs1 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & Hs1c & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  pose proof (a5B_start cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd ql Eq3 HB HJ HW HAT
                ltac:(lia) HEdef B18) as KST.
  pose proof (a5B_end POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd ql HN HB HFR HRc
                HRm HRa Hc Hci Hj Hm Hk Hkd Hl Hhd HW HAT) as KFIN.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose proof (a5_shok_fl cx fpos k2 ly3 S3 md3 W3 (ms_mem ms3) Eq3 HB HJB
                (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) B20 B21) as SHOK.
  destruct (Z.eq_dec (qn mod 4) 0) as [Hz|Hz].
  - (* n a multiple of 4: one run to the latch *)
    destruct (KST true Hz) as (HS & HAWR).
    paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_ALAT); [exact HAWR|].
    lazymatch goal with
    | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
      HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      let HR1 := fresh "HR1" in
      spregion HS' 1%nat HR1;
      apply (KFIN E msn mdn _ B21 B32 B33 B18 HR1);
      [ intros q Hq Hnq;
        apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem msn)
                 (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr');
        [exact (a5B_windows E true (kW2 cx fpos) BV21) | exact Hq | intros Hc'; apply Hnq; left; exact Hc']
      | intros q Hq; exact (k3_apres_grows _ _ _ q HG' Hq)
      | assumption
      | apply (kn_kms_of _ E ssx msn KP_ALAT HS'); vm_compute; reflexivity
      | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
      | exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24; 22]%nat)
                 HS' HAG ltac:(vm_compute; reflexivity))
      | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
      | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
      | a5_md
      | a5_md
      | kn_in
      | kn_in ]
    end.
  - (* else: a run to the call, checked_memset(w2 + n, 0, pad), a run to the latch *)
    destruct (KST false Hz) as (HS & HAWR).
    pose proof HS as HS0.
    paj_run_tok RUN HS HJ SHOK k3_span; [exact HAWR|].
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1; rename HSx into HS1 end.
    lazymatch goal with HFx : frame_of _ _ _ _ |- _ => rename HFx into HFr1 end.
    lazymatch goal with HGx : mem_grows _ _ |- _ => rename HGx into HG1 end.
    assert (UN1 : forall q, 0 <= q < 2 ^ 64 -> ~ (kW2 cx fpos <= q < kW2 cx fpos + NW_SIZE) ->
              aview SEGS (w_H W3) (ms_mem ms1) q = aview SEGS (w_H W3) (ms_mem ms3) q).
    { intros q Hq Hnq.
      apply (kept_of_frame (segs := SEGS) Eq3 _ (w_H W3) (ms_mem ms3) (ms_mem ms1)
               (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr1);
        [exact (a5B_windows Eq3 false (kW2 cx fpos) BV21) | exact Hq | exact Hnq]. }
    pose proof (fun q Hq => k3_apres_grows _ _ _ q HG1 Hq) as P1.
    pose proof (a5_reg_same Eq3 _ _ (w_H W3) ms3 ms1 [2; 3; 4] HS0 HS1 ltac:(vm_compute; reflexivity)) as KEEP.
    sreg HS1 (10%bv : bv 5) R10. sreg HS1 (11%bv : bv 5) R11. sreg HS1 (12%bv : bv 5) R12.
    prreg HS1 (1%bv : bv 5) R1.
    cbn [ms_regs restrict mkst] in R10, R11, R12.
    pmkst HS1.
    rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memset) with 0x53214.
    eapply (a5_call_ms cx fpos k2 ly3 S3 W3 ms3 md3 (ms_mem ms1) _ (ms_regs ms1) _ qn ((qn + 3) / 4 * 4 - qn)
              (POST cx) HB HJ HJB HSH UN1);
      [ lia | lia | unfold NW_SIZE; lia
      | rewrite R10; cbn [sv_denot]; rewrite B34, Z.add_0_r; reflexivity
      | rewrite R11; reflexivity
      | rewrite R12, denot_lit_U, (a5_U_len Eq3 qn 0 3 B32 eq_refl ltac:(lia)), !Z.add_0_r; reflexivity
      | rewrite (KEEP 2%bv) by reflexivity; exact (proj1 HR0)
      | rewrite (KEEP 3%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 HR0))))
      | rewrite (KEEP 4%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 (proj2 HR0)))))
      | exact R1
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | ].
    intros regs2 mem2 md2 HJ2 HP2 Hfr2 Hpres2 Hsbm.
    jafter_call_keep_pi HS1 40%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 1]%nat HS2.
    lazymatch type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { destruct HFRM as (_ & _ & _ & _ & HFP & _).
      cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B9; intros q Hq.
        + apply kn_mbyte_of_aview. apply Hfr2; [lia | lia | rewrite HES; lia].
        + lia.
      - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B21; intros q Hq.
        + apply kn_mbyte_of_aview. apply Hfr2; [lia | lia | rewrite HES; lia].
        + intros _. apply kn_apresent_writable. apply Hpres2, P1, HFP. rewrite kn_fsb8. lia. }
    rewrite <- restrict_mkst_fx in HS2.
    remember (havoc Eq3 40 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS2.
    assert (HEI2 : img_env pa_val A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (HAG2 : env_agree 32 (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk)) E2)
      by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAG]).
    assert (C21 : bv_unsigned (ew E2 21) = kW2 cx fpos) by (rewrite HE2, ew_havoc_old by lia; exact B21).
    assert (C32 : bv_unsigned (ew E2 32) = qn) by (rewrite HE2, ew_havoc_old by lia; exact B32).
    assert (C33 : bv_unsigned (ew E2 33) = qf) by (rewrite HE2, ew_havoc_old by lia; exact B33).
    assert (C18 : bv_unsigned (ew E2 18) = ka0 cx) by (rewrite HE2, ew_havoc_old by lia; exact B18).
    assert (C20 : bv_unsigned (ew E2 20) = SHADOW_OFF) by (rewrite HE2, ew_havoc_old by lia; exact B20).
    assert (CV21 : base_val E2 (Some 21%nat) = kW2 cx fpos) by exact C21.
    clear HE2.
    (* the memory after the call, against the cut's: changed only in w2 and the callee's window *)
    assert (UNc : forall q, 0 <= q < 2 ^ 64 ->
              ~ ((kW2 cx fpos <= q < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= q < ksp1 cx)) ->
              aview SEGS (w_H W3) mem2 q = aview SEGS (w_H W3) (ms_mem ms3) q).
    { intros q Hq Hnq.
      rewrite (Hfr2 q Hq ltac:(intros Hc'; apply Hnq; left; unfold NW_SIZE; lia)
                 ltac:(intros Hc'; apply Hnq; right; exact Hc')).
      apply UN1; [exact Hq | intros Hc'; apply Hnq; left; exact Hc']. }
    pose proof (a5_shok_fl cx fpos k2 ly3 S3 md3 W3 mem2 E2 HB HJB
                  (a5_w2_ra cx fpos k2 ly3 S3 md3 W3 ms3 mem2 HB HJB HSH UNc) C20 C21) as SHOK2.
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 k3_span (kpc KP_ALAT).
    { cbn [ss_mem].
      apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
      apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite CV21 in Hx.
      left. apply (a5_awf cx fpos k2 ly3 S3 W3 _ _ HB HJ2). unfold NW_SIZE. lia. }
    lazymatch goal with
    | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
      HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      let HR1 := fresh "HR1" in
      spregion HS' 1%nat HR1;
      apply (KFIN E msn mdn _ C21 C32 C33 C18 HR1);
      [ intros q Hq Hnq;
        rewrite (kept_of_frame (segs := SEGS) E _ (w_H W3) mem2 (ms_mem msn)
                   (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr' ltac:(
                     intros b wlo whi x Hin Hx; unfold windows in Hin;
                     cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
                     destruct Hin as [Hq' | [Hq' | []]]; injection Hq' as <- <- <-;
                     [lia | rewrite CV21 in Hx; unfold NW_SIZE; lia])
                   q Hq ltac:(intros Hc'; apply Hnq; left; exact Hc'));
        exact (UNc q Hq Hnq)
      | intros q Hq; exact (k3_apres_grows _ _ _ q HG' (Hpres2 q (P1 q Hq)))
      | assumption
      | apply (kn_kms_of _ E ssx msn KP_ALAT HS'); vm_compute; reflexivity
      | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG2 ltac:(vm_compute; reflexivity))
      | exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24; 22]%nat)
                 HS' HAG2 ltac:(vm_compute; reflexivity))
      | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
      | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
      | rewrite ?(proj1 (wvb_fds_fs _ _ _)), (proj1 (kn_sbm_fds_fs _ _ Hsbm)); a5_md
      | rewrite ?(proj2 (wvb_fds_fs _ _ _)), (proj2 (kn_sbm_fds_fs _ _ Hsbm)); a5_md
      | kn_in
      | kn_in ]
    end.
Qed.

(* ---- THE LEMMA ---- *)
Theorem kn_a5 : forall POST (Rc Rm Ra : kcx -> Z -> Prop),
  kfrom SK B POST (kin_alat B Rc Rm Ra) -> kfrom SK B POST (kin_acase B Rc Rm Ra KP_A5 ka_5).
Proof. intros POST Rc Rm Ra HN. exact (a5_put POST Rc Rm Ra (a5_padl POST Rc Rm Ra HN)). Qed.

End b.
End a.

Print Assumptions kn_a5.
