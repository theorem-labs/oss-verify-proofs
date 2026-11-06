(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the message of kind 3
   (lib/A/Prog/kernel_defs.v kin_kind at kd = 3, +0x1150) to the cut after a message (kin_next, +0x1b84). Listing
   (internal path) (internal record, sha256 7bc02d6772b3), +0x1150 .. +0x1b84.

   THE CODE. Kind 3 calls nothing (the checked_memset of nl_pad at +0x113c is not reached from +0x1150). It puts six
   fields into w2 at w2 + n (n = w2.n): a 4-byte length word, two 2-byte fields and three 4-byte fields. Each put is
   behind a room test `bltu (2^64 - 4098), n + L - 4097` (taken when n + L <= 4096): taken, it stores L bytes at
   w2 + n and n += L; not taken, it stores w2.full := 1 and goes on to the next test. Then a test `bltu n', n + 4`
   skips the length back-fill if the length word was not put; else it stores n' - n at w2 + n. +0x1b80
   `ld a4, 0xa0(s1)` reloads k; the phase ends at +0x1b84 with a4 = k.

   THE STATE. The symbolic state at the kind's entry has the registers sr_atoms but s9 (= w2 + 4096, so the fields
   are read through s5's atom); the extra atoms 32 = n, 33 = full, 34 = w2 + n, 35 = k (k3_ext); three regions: the
   spill slots 0xa0 (k), 0xc8 (&w2.full), 0xd0 (2^64 - 4098), 0xd8 (2^64 - 4093) read-only; w2's two fields,
   writable; the pl bytes the group puts at w2 + n, writable; the alias w2 + n = atom 34. The shadow entries are w2's
   fields and the put bytes (pl + 8 bytes from w2 + n), both addressable since F's shadow is kfsh f8 0 f3
   (kernel_kit.v kn_w2_ra). The room tests wrap, so the engine cannot decide a taken one from the atoms' ranges: the
   taken tests of each group are in the facts' conditions (k3_conds, each true by k3_cond_ok), and the not-taken
   ones the engine decides from n's range.

   THE GROUPS (n at the cut; pl the bytes put; the taken tests' offsets c of `n + c`):
     n <= 4076: pl 20, all six | 4077..4080: 16, five | 4081..4084: 12, four | 4085..4088: 8, three |
     4089..4090: 6, two | 4091..4092: 4, one | 4093..4094: 2, the first 2-byte field only | 4095..4096: 0, none.
   Each group is ONE run (LinkWalk paj_run_to_x) to +0x1b84. At the end w2.n = n + pl, w2.full = full (pl = 20) or 1.

   THE CUT RE-ESTABLISHED. The run writes only inside [w2, w2 + NW_SIZE), so kernel_kit.v kat_frame_w2 moves every
   memory clause of the cut; kw_move gives w2's new fields from the end state's field region.

   Callees: none. Section hypothesis used: LAWS : AR_laws pa_segs B (the lib/A frame; the run instances need it).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_defs kernel_kit kernel_next.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at +0x1150 ---- *)
Definition k3_Bx : sv := SOff 20 0.
Definition k3_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition k3_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xa0 0xe0 0 0
    [YP09.mkChunk 0xa0 (CVal 8 (SOff 35 0)); YP09.mkChunk 0xc8 (CVal 8 (SOff 21 4104));
     YP09.mkChunk 0xd0 (CVal 8 (SLit (2 ^ 64 - 4098))); YP09.mkChunk 0xd8 (CVal 8 (SLit (2 ^ 64 - 4093)))].
Definition k3_fl : YP09.region :=
  YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112
    [YP09.mkChunk 4096 (CVal 8 (SOff 32 0)); YP09.mkChunk 4104 (CVal 4 (SOff 33 0))].
Definition k3_pr (pl : Z) : YP09.region := YP09.mkRegion (Some 34%nat) 0 pl 0 pl [].
(* the taken room tests: n + c with -4098 < n + c < 0 *)
Definition k3_conds (cs : list Z) : list acond :=
  map (fun c => mkAC BC_LTU (SLit (2 ^ 64 - 4098)) (SOff 32 c)) cs.
Definition k3_facts (lo hi : Z) (cs : list Z) : facts :=
  mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (21%nat, mkAF 4096 (2 ^ 47 - 4113) 0);
           (32%nat, mkAF lo hi 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 4096 (2 ^ 47 - 4113) 0)]
    (k3_conds cs) [(SAlu ALU_ADD (SOff 21 0) (SOff 32 0), SOff 34 0)].
Definition k3_regs : list sv := sr_set sr_atoms (Z_to_bv 5 (Z.of_nat 25)) (SOff 21 4096).
Definition k3_ss (lo hi pl : Z) (cs : list Z) : sstate :=
  mkSS (kpc KP_K3) k3_regs [k3_sp; k3_fl; k3_pr pl] None (k3_facts lo hi cs).
Definition k3_SH (pl : Z) : list shent := [mkSHE 21 4096 4112; mkSHE 34 0 (pl + 8)].

(* ---- the room tests ---- *)
Lemma k3_cond_ok : forall E n c, bv_unsigned (ew E 32) = n -> -4098 < n + c < 0 ->
  acond_ok E (mkAC BC_LTU (SLit (2 ^ 64 - 4098)) (SOff 32 c)).
Proof.
  intros E n c Hn Hc. unfold acond_ok. cbn [ac_c ac_a ac_b sv_denot branch_taken].
  rewrite bv_ltu_unsigned, Hn. rewrite (unsigned_lit_small (2 ^ 64 - 4098)) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (n + c) with ((n + c + 2 ^ 64) + (-1) * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  apply Z.ltb_lt. lia.
Qed.

Lemma k3_conds_ok : forall E n cs, bv_unsigned (ew E 32) = n ->
  Forall (fun c => -4098 < n + c < 0) cs -> conds_ok E (k3_conds cs).
Proof.
  intros E n cs Hn H. induction H as [|c cs Hc _ IH]; [exact I|].
  cbn [k3_conds map conds_ok]. split; [exact (k3_cond_ok E n c Hn Hc) | exact IH].
Qed.

(* the windows of the state lie in w2 *)
Lemma k3_windows : forall (E : env) lo hi pl cs w n,
  base_val E (Some 21%nat) = w -> base_val E (Some 34%nat) = w + n -> 0 <= n -> 0 <= pl -> n + pl <= 4096 ->
  forall b wlo whi a, In (b, wlo, whi) (windows (ss_mem (k3_ss lo hi pl cs))) ->
    base_val E b + wlo <= a < base_val E b + whi -> w <= a < w + NW_SIZE.
Proof.
  intros E lo hi pl cs w n H21 H34 Hn Hpl Hnpl b wlo whi a Hin Ha.
  unfold k3_ss, windows in Hin.
  cbn [ss_mem map In k3_sp k3_fl k3_pr YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  unfold NW_SIZE.
  destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-.
  - lia.
  - rewrite H21 in Ha. lia.
  - rewrite H34 in Ha. lia.
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

Definition k3_ext (cx : kcx) (fpos n f k : Z) : list word :=
  [w64 n; w64 f; w64 (kW2 cx fpos + n); w64 k].

(* ---- byte and word helpers (kernel_setup.v's su_ lemmas) ---- *)
Lemma k3_apres_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a Hg (Hh & b & Hb). split; [exact Hh|].
  specialize (Hg (Z_to_bv 64 a)). unfold mrestrict in Hg. rewrite Hh in Hg.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|].
  exfalso. apply Hg; [rewrite Hb; discriminate | reflexivity].
Qed.

Lemma k3_rdword_range : forall (H : word -> bool) (m : word -> option byte) a v,
  rdword (aview SEGS H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros H m a v Hv.
  assert (R : forall x b, aview SEGS H m x = Some b -> 0 <= b < 256).
  { intros x b Hb. destruct (aview_byte SEGS H m x b Hb) as (_ & _ & _ & Hr). exact Hr. }
  unfold rdword in Hv.
  destruct (aview SEGS H m a) as [b0|] eqn:E0; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 1)) as [b1|] eqn:E1; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 2)) as [b2|] eqn:E2; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 3)) as [b3|] eqn:E3; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 4)) as [b4|] eqn:E4; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 5)) as [b5|] eqn:E5; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 6)) as [b6|] eqn:E6; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 7)) as [b7|] eqn:E7; [|cbv iota beta in Hv; discriminate Hv].
  cbv iota beta in Hv. injection Hv as <-.
  apply R in E0. apply R in E1. apply R in E2. apply R in E3.
  apply R in E4. apply R in E5. apply R in E6. apply R in E7. lia.
Qed.

(* a spill slot's 8 bytes as a chunk of the state's region *)
Lemma k3_chunk_rd : forall E (H : word -> bool) (mm : word -> option byte) base off e v,
  sv_denot E e = Z_to_bv 64 v -> rdword (aview SEGS H mm) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H mm) base (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E H mm base off e v He Hr.
  pose proof (k3_rdword_range H mm (base + off) v Hr) as Hv.
  apply (chunk_ok_val SEGS E (mrestrict H mm) base off 8 e v He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
  - exact (val_mem_of_rdword SEGS H mm (base + off) v Hr).
Qed.

(* ---- the environment at +0x1150 ---- *)
Lemma k3_env : forall cx fpos k2 ly3 S3 md3 (ms3 : machine_state) n f k (E : env),
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kregs0 cx ms3 ->
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 21)) = w64 (kW2 cx fpos) ->
  0 <= n <= 4096 -> 0 <= f <= 1 -> 0 <= k < 5 ->
  E = Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos n f k)) ->
  bv_unsigned (ew E 9) = ksp1 cx /\ bv_unsigned (ew E 20) = SHADOW_OFF /\
  bv_unsigned (ew E 21) = kW2 cx fpos /\ bv_unsigned (ew E 32) = n /\ bv_unsigned (ew E 33) = f /\
  bv_unsigned (ew E 34) = kW2 cx fpos + n /\ bv_unsigned (ew E 35) = k.
Proof.
  intros cx fpos k2 ly3 S3 md3 ms3 n f k E HB HJB HR0 R21 Hn Hf Hk HEdef.
  destruct HR0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & _ & Hs1b & _ & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hj; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hj)).
  assert (EXT : forall jn, (jn < 4)%nat -> ew E (32 + jn) = nth jn (k3_ext cx fpos n f k) (Z_to_bv 64 0))
    by (intros jn Hj; rewrite HEdef, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
  pose proof (EXT 2%nat ltac:(lia)) as E34. pose proof (EXT 3%nat ltac:(lia)) as E35.
  cbn [k3_ext nth Nat.add] in E32, E33, E34, E35.
  assert (E9 : ew E 9 = w64 (ksp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact R9).
  assert (E20 : ew E 20 = w64 SHADOW_OFF) by (rewrite (ER 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = w64 (kW2 cx fpos))
    by (rewrite (ER 21%nat (Z_to_bv 5 (Z.of_nat 21)) eq_refl); exact R21).
  split; [rewrite E9; apply unsigned_lit_small; lia|].
  split; [rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia|].
  split; [rewrite E21; apply unsigned_lit_small; lia|].
  split; [rewrite E32; apply unsigned_lit_small; lia|].
  split; [rewrite E33; apply unsigned_lit_small; lia|].
  split; [rewrite E34; apply unsigned_lit_small; lia|].
  rewrite E35; apply unsigned_lit_small; lia.
Qed.

(* U of an atom at offset 0 *)
Lemma k3_U0 : forall (E : env) (mt : nat) p, bv_unsigned (ew E mt) = p -> 0 <= p < 2 ^ 64 -> U E (SOff mt 0) = p.
Proof.
  intros E mt p Hp Hr. unfold U. cbn [sv_denot]. rewrite Hp, Z.add_0_r. apply unsigned_lit_small. exact Hr.
Qed.

(* ---- THE START: the symbolic state, its shadow entries and its writable windows at +0x1150 ---- *)
Lemma k3_start : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 c ci j m k n f adv (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K3
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
     (22%nat, m); (16%nat, 3)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  0 <= k < m -> m <= 5 ->
  E = Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos n f k)) ->
  forall lo hi pl cs,
  lo <= n <= hi -> 0 <= pl -> n + pl <= 4096 ->
  regions_wf [k3_sp; k3_fl; k3_pr pl] = true ->
  Forall (fun c => -4098 < n + c < 0) cs ->
  st_ok_pi SEGS pa_val E (k3_ss lo hi pl cs) (restrict (w_H W3) ms3) /\
  sh_ok SEGS k3_Bx (k3_SH pl) E (mrestrict (w_H W3) (ms_mem ms3)) /\
  awr_ok_x E (ss_mem (k3_ss lo hi pl cs)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv E HB HJ HW HAT Hk Hm5 HEdef lo hi pl cs Hn Hpl Hnpl
    Hwf Hcs.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  pose proof (kn_reg_of ms3 _ 25 (kW2 cx fpos + NW_N) HRL ltac:(kn_in)) as R25.
  destruct HW as (Hw0 & Hwl & Hpres & Hnv & Hfv & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  destruct (k3_env cx fpos k2 ly3 S3 md3 ms3 n f k E HB HJB HR0 R21 ltac:(lia) Hfr ltac:(lia) HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _ & HFsh).
  pose proof (kn_sp SK B cx HB) as (Hac & _ & _ & Hs1 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & _ & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof kn_band as (KB1 & KB2).
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact B9.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV34 : base_val E (Some 34%nat) = kW2 cx fpos + n) by exact B34.
  (* the spill slots the state reads *)
  pose proof (kn_slot_of cx W3 ms3 _ KS_K k HSL ltac:(apply in_or_app; right; kn_in)) as SL_K.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W2F (kW2 cx fpos + NW_FULL) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_W2F.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4098 (2 ^ 64 - 4098) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_M4098.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4093 (2 ^ 64 - 4093) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_M4093.
  (* F, the side frame, at the current layout *)
  pose proof HB as (HPRE & _). pose proof HPRE as (HJ0 & _).
  assert (HFA : frame_addr ly3 KN_CID fpos = kF cx fpos).
  { destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos HJ)
      as (HA1 & _).
    destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos HJ0)
      as (HA2 & _).
    unfold kF. now rewrite HA1, HA2. }
  assert (AWF : forall x, kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE ->
            awr_byte (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3
              ((KN_CID, fpos) :: k_own cx) x /\ ~ (k_sp0 cx <= x < k_sp0 cx + k_XO cx)).
  { intros x Hx.
    apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos x HJ).
    - left. reflexivity.
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFA, kn_fsb8. unfold NW_SIZE in Hx. lia. }
  (* w2's shadow bytes are 0 *)
  pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HRA.
  split; [|split].
  - (* the symbolic state *)
    rewrite (kn_ms_shape ms3 (BASE + kpc KP_K3) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold k3_ss. apply pa_entry_st_ok_full.
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
    unfold k3_ss. cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; unfold k3_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    + intros x Hx. unfold k3_fl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV21 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
    + intros x Hx. unfold k3_pr in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV34 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
Qed.

(* ---- THE END: the cut after a message, from the end state's facts ---- *)
Lemma k3_cut : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    (ms : machine_state) md c ci j m k n f adv n' f',
  kfrom SK B POST (kin_next B Rc Rm) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K3
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
     (22%nat, m); (16%nat, 3)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  kms KP_NEXT ms -> kregs0 cx ms ->
  (forall r, In r [21; 24; 22]%nat ->
     getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 25)) = w64 (kW2 cx fpos + NW_N) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 14)) = w64 k ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms) a) ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (kW2 cx fpos + NW_N) 8 n' ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (kW2 cx fpos + NW_FULL) 4 f' ->
  0 <= n' <= NL_CHUNK_MAX -> 0 <= f' <= 1 ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 ms md c ci j m k n f adv n' f' HN HB HJ HFR HRc HRm Hc Hci Hj
    Hm Hk HW HAT HMS HR0 HK H25 H14 Hfds Hfs UN HP Hn Hf Hnr Hfr.
  pose proof HAT as (_ & _ & HRL & _).
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  exists c, ci, j, m, k, n', f', adv.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hm|]. split; [exact Hk|].
  split; [exact (kw_move W3 ms3 W3 ms (kW2 cx fpos) n f n' f' HW HP Hn Hf Hnr Hfr)|].
  apply (kat_frame_w2 SK B LAWS 0 NW_SIZE cx fpos KP_K3 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 KP_NEXT _ _
           W3 ms md HB HAT HMS HR0).
  - unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    + rewrite (HK 21%nat) by kn_in. apply (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL). kn_in.
    + rewrite (HK 24%nat) by kn_in. apply (kn_reg_of ms3 _ 24 (kS8 cx) HRL). kn_in.
    + exact H25.
    + exact H14.
    + rewrite (HK 22%nat) by kn_in. apply (kn_reg_of ms3 _ 22 m HRL). kn_in.
  - intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact Hx|].
    right. cbn [In] in Hx |- *. tauto.
  - reflexivity.
  - apply kfsh_fits.
  - exact Hfds.
  - exact Hfs.
  - lia.
  - lia.
  - intros a Ha Hna. apply UN; [exact Ha|]. intros Hc'. apply Hna. lia.
  - exact HP.
Qed.

(* the end in the form the run's results give it: the end state's field region and frame, the registers kept *)
Lemma k3_end : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv (E : env),
  kfrom SK B POST (kin_next B Rc Rm) ->
  kbase SK B cx ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K3
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
     (22%nat, m); (16%nat, 3)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  bv_unsigned (ew E 21) = kW2 cx fpos -> bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 33) = f ->
  bv_unsigned (ew E 34) = kW2 cx fpos + n -> bv_unsigned (ew E 35) = k ->
  forall lo hi pl cs, 0 <= pl -> n + pl <= 4096 ->
  forall (ms : machine_state) md cs' fe f',
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs') ->
  frame_of E (ss_mem (k3_ss lo hi pl cs)) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  kms KP_NEXT ms ->
  (forall r, In r nx_keep0 -> getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  (forall r, In r (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24; 22]%nat) ->
     getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 25)) = sv_denot E (SOff 21 4096) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 14)) = sv_denot E (SOff 35 0) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  In (YP09.mkChunk 4096 (CVal 8 (SOff 32 pl))) cs' ->
  In (YP09.mkChunk 4104 (CVal 4 fe)) cs' ->
  (fe = SOff 33 0 /\ f' = f) \/ (fe = SLit 1 /\ f' = 1) ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv E HN HB HFR HRc HRm Hc Hci Hj Hm Hk HW HAT
    B21 B32 B33 B34 B35 lo hi pl cs Hpl Hnpl ms md cs' fe f' HR1 HFr HG HJ HMS HK0 HKN H25 H14 Hfds Hfs Hin1 Hin2
    Hfe.
  pose proof HAT as (_ & HR0 & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV34 : base_val E (Some 34%nat) = kW2 cx fpos + n) by exact B34.
  assert (Hf' : 0 <= f' <= 1) by (destruct Hfe as [(_ & ->) | (_ & ->)]; lia).
  apply (k3_cut POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 ms md c ci j m k n f adv (n + pl) f' HN HB HJ HFR HRc HRm
           Hc Hci Hj Hm Hk HW HAT HMS).
  - exact (kregs0_keep cx ms3 ms HK0 HR0).
  - intros r Hr. exact (HKN _ (kn_in_map5 r _ Hr)).
  - rewrite H25. cbn [sv_denot]. rewrite B21. reflexivity.
  - rewrite H14. cbn [sv_denot]. rewrite B35, Z.add_0_r. reflexivity.
  - exact Hfds.
  - exact Hfs.
  - intros a Ha Hna.
    apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms)
             (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr);
      [exact (k3_windows E lo hi pl cs (kW2 cx fpos) n BV21 BV34 ltac:(lia) Hpl Hnpl) | exact Ha | exact Hna].
  - intros a Ha. exact (k3_apres_grows _ _ _ a HG Ha).
  - exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4096 8 (SOff 32 pl) (n + pl) HR1 B21 Hin1
             ltac:(cbn [sv_denot]; rewrite B32; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
  - destruct Hfe as [(-> & ->) | (-> & ->)].
    + exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SOff 33 0) f HR1 B21 Hin2
               ltac:(cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
    + exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SLit 1) 1 HR1 B21 Hin2
               eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  - unfold NL_CHUNK_MAX. lia.
  - exact Hf'.
Qed.

(* ---- the run of one group, from the start to the end (KST: k3_start at the cut, KFIN: k3_end at the cut) ---- *)
Ltac k3_go KST KFIN RUNTO HJ HAG lo hi pl cs fv fe :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAWR := fresh "HAWR" in
  destruct (KST lo hi pl cs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              ltac:(repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil)) as (HS & SHOK & HAWR);
  paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_NEXT); [exact HAWR|];
  lazymatch goal with
  | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
    HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
    HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    let HR1 := fresh "HR1" in
    spregion HS' 1%nat HR1;
    apply (KFIN lo hi pl cs ltac:(lia) ltac:(lia) msn mdn _ fe fv HR1 HFr' HG');
    [ assumption
    | apply (kn_kms_of _ E ssx msn KP_NEXT HS'); vm_compute; reflexivity
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24; 22]%nat)
               HS' HAG ltac:(vm_compute; reflexivity))
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | exact (proj1 (wvb_fds_fs _ _ _))
    | exact (proj2 (wvb_fds_fs _ _ _))
    | kn_in
    | kn_in
    | first [left; split; reflexivity | right; split; reflexivity] ]
  end.

(* ---- the phase ---- *)
Theorem kn_k3 : forall POST (Rc Rm : kcx -> Z -> Prop),
  kfrom SK B POST (kin_next B Rc Rm) -> kfrom SK B POST (kin_kind B Rc Rm 3).
Proof.
  intros POST Rc Rm HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qc & qci & qj & qm & qk & qn & qf & qadv & HRc & HRm & Hc & Hci & Hj & Hm & Hk & _ & HW & _ & HAT).
  change (kind_pc 3) with KP_K3 in HAT.
  pose proof HAT as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  remember (Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk))) as Eq3 eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM Eq3) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk)) Eq3)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (k3_env cx fpos k2 ly3 S3 md3 ms3 qn qf qk Eq3 HB HJB HR0 R21 ltac:(lia) Hfr ltac:(lia) HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  pose proof (k3_start cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv Eq3 HB HJ HW HAT
                ltac:(lia) ltac:(lia) HEdef) as KST.
  pose proof (k3_end POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv Eq3 HN HB HFR HRc HRm
                Hc Hci Hj Hm Hk HW HAT B21 B32 B33 B34 B35) as KFIN.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  destruct (Z_le_gt_dec qn 4076) as [G|G];
    [k3_go KST KFIN RUNTO HJ HAG 0 4076 20 ([-4093; -4091; -4089; -4085; -4081; -4077]) qf (SOff 33 0)|].
  destruct (Z_le_gt_dec qn 4080) as [G'|G'];
    [k3_go KST KFIN RUNTO HJ HAG 4077 4080 16 ([-4093; -4091; -4089; -4085; -4081]) 1 (SLit 1)|].
  destruct (Z_le_gt_dec qn 4084) as [G''|G''];
    [k3_go KST KFIN RUNTO HJ HAG 4081 4084 12 ([-4093; -4091; -4089; -4085]) 1 (SLit 1)|].
  destruct (Z_le_gt_dec qn 4088) as [G3|G3];
    [k3_go KST KFIN RUNTO HJ HAG 4085 4088 8 ([-4093; -4091; -4089]) 1 (SLit 1)|].
  destruct (Z_le_gt_dec qn 4090) as [G4|G4];
    [k3_go KST KFIN RUNTO HJ HAG 4089 4090 6 ([-4093; -4091]) 1 (SLit 1)|].
  destruct (Z_le_gt_dec qn 4092) as [G5|G5]; [k3_go KST KFIN RUNTO HJ HAG 4091 4092 4 ([-4093]) 1 (SLit 1)|].
  destruct (Z_le_gt_dec qn 4094) as [G6|G6]; [k3_go KST KFIN RUNTO HJ HAG 4093 4094 2 ([-4095]) 1 (SLit 1)|].
  k3_go KST KFIN RUNTO HJ HAG 4095 4096 0 (@nil Z) 1 (SLit 1).
Qed.

End b.
End a.

Print Assumptions kn_k3.
