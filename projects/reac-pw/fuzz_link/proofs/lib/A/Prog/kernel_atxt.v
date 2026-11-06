(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v; 1071 of its 1135 lines of code are new or changed and 422 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's ATTRIBUTE LOOP HEAD, kin_attr (+0x9d8) -> kin_txt (+0xa74) /
   kin_acase KP_A0 ka_empty (+0xb10) (link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7) section 4;
   link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5)).

   WHAT THE CODE DOES HERE (listing (internal path) (internal record, sha256 7bc02d6772b3); the
   inlined fuzz_u8 of the attribute byte and the texts load):
     +0x9d8  lbu a0, 0(s8); beqz a0        the instrumented check of the cursor's n word (s8 = shadow(a0 + 8))
     +0x9e4  ld a0, 0(s3)                  n, the bytes left (s3 = a0 + 8)
     +0x9e8  beqz a0 -> +0xac8: the empty cursor: s7 := 0, s11 := .str.1 (texts[0], folded), j +0xb10 (kin_acase
             KP_A0 ka_empty; nothing written)
     +0x9ec  the check again; sd n - 1, 8(s2); the check of p (slot KS_CSH); sd p + 1, 0(s2)
     +0xa1c  the instrumented check of the input byte at p: a1 := lb ((p >> 3) + s4); `bnez a1` -> +0xf88: `andi a2,
             a0, 7; blt a2, a1` -> +0xa2c, else the error path
     +0xa2c  lbu s7, 0(a0): the attribute byte a
     +0xa30  the magic 0x1745d1745d1745d2 (`ld` from .rodata 0x10318); (a >> 3) % 11 by mulhu; a0 := texts + 8 *
             ((a >> 3) % 11) (texts = .data.rel.ro 0xa17c0); the check of that word (s = 0 only); +0xa70 ld s11, 0(a0)
     +0xa74  the cut kin_txt.

   THE PROOF. The empty cursor is one run from the state at +0x9d8 (kernel_head.v's state, the cursor region alone).
   Otherwise the run has two stages. Stage 1, from +0x9d8 to +0xa30: kernel_head.v's state (the cursor, the slot
   KS_CSH, the input byte at p and its shadow byte with the alias (p >> 3) + s4 = q), split up front on the input
   byte's shadow byte (s = 0, or s <> 0 with (p & 7) < s: saddr_ok of the input's range_addressable). Stage 2, from
   +0xa30 to +0xa74, from a fresh state over the machine state stage 1 ended in (registers sr_atoms, so s7 = the
   byte a is atom 23): the magic's word (KernImg, kernel_img.v ki_m11_val_mem, at arodata_okP), the texts word at
   T = texts + 8 * ((a >> 3) % 11) as atom 32 with the alias of the code's address expression (at_idx_U), its check
   by the SH entry (T, 0, 8) (kernel_apre's range_addressable of texts, moved to the current state). The input byte is
   not in stage 2's regions: kernel_apre separates the input from kernel's writes, not from .rodata / texts. The cut
   is read off the end state with kernel_kit.v's frame lemmas over the run's frame: it writes only the cursor (at_land).

   Section hypotheses: LAWS : AR_laws pa_segs B (the lib/A frame); LV : LinkVals (the image's object addresses);
   KI : KernImg pa_segs B (kernel_img_tfib.v kernel_img_syms); TB : PcapSyms B (AF0m.v; AD2l.PcapB_syms).
   Released proofs (rule 24): this proves no function (kind: segment lemma of kernel's walk); the walk of kernel had
   its search (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PcapRelro kernel_c kernel_img kernel_defs kernel_kit kernel_head.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic states ----
   Stage 1 and the empty cursor: kernel_head.v's atoms (32 = p, 33 = n, 34 = d the byte at p, 35 = q = shadow(p),
   36 = s the shadow byte at q), its registers (s3 = a0 + 8, s8 = shadow(a0 + 8)), its cursor and input regions; the
   slot KS_CSH alone (nothing writes a slot here). *)
Definition at_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0xc0 0xc0 [YP09.mkChunk 0xc0 (CVal 8 (hd_sh 18 0))].
Definition at_rs1 : smem := [hd_cur 16 (SOff 33 0); at_slots; hd_in; hd_ish].
(* n <> 0 (+0x9e8) and the input byte's check (+0xa28, +0xf8c) *)
Definition at_cs (fast : bool) : list acond :=
  if fast then [mkAC BC_NE (SOff 33 0) (SLit 0); mkAC BC_EQ (SOff 36 0) (SLit 0)]
  else [mkAC BC_NE (SOff 33 0) (SLit 0); mkAC BC_NE (SOff 36 0) (SLit 0);
        mkAC BC_LT (SAlu ALU_AND (SOff 32 0) (SLit 7)) (SOff 36 0)].
Definition at_ss1 (fast : bool) : sstate :=
  mkSS (kpc KP_ATTR) hd_regs at_rs1 None (mkFacts hd_atoms (at_cs fast) hd_alias).
Definition at_rs0 : smem := [hd_cur 0 (SLit 0)].
Definition at_ss0 : sstate := mkSS (kpc KP_ATTR) hd_regs at_rs0 None (mkFacts hd_atoms [] hd_alias).
(* Stage 2, from +0xa30: registers sr_atoms (s7 = atom 23 = a); 32 = T the texts word's address, 33 = its value *)
Definition at_idx (r : nat) : sv :=
  SAlu ALU_SLL
    (SAlu ALU_SUB (SAlu ALU_SRL (SOff r 0) (SLit 3))
       (SMd M_MUL (SMd M_MULHU (SAlu ALU_SRL (SOff r 0) (SLit 3)) (SLit KI_M11_V)) (SLit 11)))
    (SLit 3).
Definition at_mg : YP09.region := YP09.mkRegion (Some (A_OBJ 18)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit KI_M11_V))].
Definition at_tx : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition at_rs2 : smem := [at_mg; at_tx].
Definition at_atoms2 : list (nat * afact) :=
  [(23%nat, mkAF 0 255 0); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF LA_TEXTS (LA_TEXTS + 80) 3)].
Definition at_alias2 : list (sv * sv) := [(SAlu ALU_ADD (SOff (A_OBJ 19) 0) (at_idx 23), SOff 32 0)].
Definition at_ss2 : sstate := mkSS (kpc 0xa30) sr_atoms at_rs2 None (mkFacts at_atoms2 [] at_alias2).
Definition at_SH2 : list shent := [mkSHE 32 0 8].
(* the registers stage 2 does not write: hd_keepz and s7 *)
Definition at_keepz2 : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25].

Ltac at_inl := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma at_keep_sub : forall x, existsb (Z.eqb x) hd_keepz = true -> existsb (Z.eqb x) at_keepz2 = true.
Proof.
  intros x H. apply existsb_exists in H as (y & Hy & Hxy). apply existsb_exists. exists y. split; [|exact Hxy].
  unfold hd_keepz in Hy. unfold at_keepz2. cbn [In] in Hy |- *. tauto.
Qed.

(* the texts index the code computes from the byte a *)
Lemma at_idx_U : forall E d, ew E 23%nat = Z_to_bv 64 d -> 0 <= d < 256 -> U E (at_idx 23) = 8 * ((d / 8) mod 11).
Proof.
  intros E d H23 Hd. unfold at_idx.
  repeat (first [rewrite U_SAlu | rewrite U_SMd | rewrite U_SLit]).
  rewrite (U_atom E 23%nat d H23 ltac:(lia)).
  rewrite <- (Z2Nat.id d) by lia. assert (Hk : (Z.to_nat d < 256)%nat) by lia.
  generalize (Z.to_nat d) Hk. clear. intros k Hk.
  do 256 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis KI : KernImg pa_segs B.
Hypothesis TB : PcapSyms B.                                  (* AF0m.v; AD2l.PcapB_syms at the frame's B *)

Definition at_E1 (ms : machine_state) (p n d s : Z) : env :=
  Eimg (Ereg (ms_regs ms) [w64 p; w64 n; w64 d; w64 (SHADOW_OFF + p / 8); w64 s]).
Definition at_E2 (ms : machine_state) (T tp : Z) : env := Eimg (Ereg (ms_regs ms) [w64 T; w64 tp]).

Lemma at_objs : pa_val (A_OBJ 8) = LA_STR_EMPTY /\ pa_val (A_OBJ 18) = KI_M11 /\ pa_val (A_OBJ 19) = LA_TEXTS.
Proof.
  split; [|split]; rewrite (lv_obj LV) by (vm_compute; lia); reflexivity.
Qed.

(* ---- the phase's context: kin_attr at +0x9d8 ---- *)
Section h.
Variable cx : kcx.
Variables fpos k2 : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
Variable md3 : Model.
Variables c ci j m k n f adv hd kd left : Z.
Hypothesis HB : kbase SK B cx.
Hypothesis HJ3 : ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
  (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2.

Definition at_rl (rl : list (nat * Z)) : list (nat * Z) :=
  (19%nat, ka0 cx + 8) :: (21%nat, kW2 cx fpos) :: (24%nat, kS8 cx) :: (25%nat, kW2 cx fpos + NW_N) ::
  (22%nat, left) :: rl.
Definition at_sl : list (Z * Z) :=
  kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)].

Hypothesis HK : kat B cx fpos KP_ATTR (at_rl []) at_sl (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.
Hypothesis HW : kw_at W3 ms3 (kW2 cx fpos) n f.

Lemma at_geo :
  alloc_ceiling <= ly_stk_lo (k_lyc cx) /\ ly_stk_hi (k_lyc cx) <= 2 ^ 47 /\
  ly_stk_lo (k_lyc cx) <= k_sp0 cx - k_STK cx /\ k_sp0 cx <= ly_stk_hi (k_lyc cx) /\
  k_sp0 cx - k_STK cx <= ksp cx - 4640 /\ ksp cx <= k_sp0 cx /\
  ksp cx - 384 < ksp1 cx <= ksp cx - 352 /\ ksp1 cx mod 32 = 0 /\ KERNEL_AK = 4640.
Proof.
  pose proof HB as (HPRE & _).
  pose proof HPRE as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
  pose proof HJ0 as (HSTK0 & HXO0 & _).
  pose proof HJ0 as HROW. eapply ajournal_gx_row in HROW. destruct HROW as (Hrow1 & Hrow2 & Hrow3 & Hrow4).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  change (spZ (k_regs cx)) with (ksp cx) in Hwlo, Hwhi. rewrite HKA in Hwlo.
  assert (Hs1 : ksp cx - 384 < ksp1 cx <= ksp cx - 352) by (unfold ksp1, ksp1_of, KN_MFRAME; lia).
  assert (Hs1al : ksp1 cx mod 32 = 0) by (unfold ksp1, ksp1_of; rewrite Z.mul_comm; apply Z_mod_mult).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [exact Hs1al | exact HKA].
Qed.

Lemma at_AR0 : AR SEGS B (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx).
Proof. pose proof HB as ((HJ0 & _) & _). pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). exact (proj1 HJi). Qed.

Lemma at_AR3 : AR SEGS B ly3 S3 W3 (ms_mem ms3) md3.
Proof. pose proof HJ3 as (_ & _ & (memS & HJi & _) & _). exact (proj1 HJi). Qed.

Lemma at_row : ly_stk_lo ly3 = ly_stk_lo (k_lyc cx) /\ ly_stk_hi ly3 = ly_stk_hi (k_lyc cx).
Proof.
  pose proof HB as ((HJ0 & _) & _).
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & Hly0 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo0 & Ehi0 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (_ & Hly3 & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo3 & Ehi3 & _).
  split; congruence.
Qed.

Lemma at_fa : forall cid pos, frame_addr ly3 cid pos = frame_addr (k_lyc cx) cid pos.
Proof.
  intros cid pos. pose proof HB as ((HJ0 & _) & _).
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & Hly0 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (_ & Hly3 & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  unfold frame_addr. rewrite EF0, EF3. reflexivity.
Qed.

Lemma at_blocks : forall b mm, In (b, mm) (ablocks B (k_lyc cx) (k_Sc cx)) -> In (b, mm) (ablocks B ly3 S3).
Proof.
  intros b mm Hin. pose proof HK as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & Hperm & _) & _).
  exact (Permutation_in _ (Permutation_sym Hperm) Hin).
Qed.

(* a byte of kernel's read set: an application byte below 2 ^ 47, not a byte of F *)
Lemma at_akb : forall a, akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) a ->
  (0 <= a < 2 ^ 47 /\ (a < kLowMemEnd \/ kHighMemBeg <= a)) /\ ~ aside_rng (k_lyc cx) KN_CID fpos a.
Proof.
  intros a Hb.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct at_geo as (Hlo & Hhi & _).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & Hjbk & _).
  destruct Hjbk as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1) & _).
  assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
  pose proof (aside_rng_low SK SEGS B LAWS pa_segs_low (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos) as Hlow.
  destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR1 Hin1) as (Hf4 & Hfc & _).
  destruct (al_flag _ _ LAWS (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR1 Hin1) as (_ & Hfo & _ & _).
  pose proof (fs_frame_bytes_nonneg KN_CID) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr (k_lyc cx) KN_CID fpos) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr (k_lyc cx) KN_CID fpos + fs_frame_bytes KN_CID) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr (k_lyc cx) KN_CID fpos) (fs_frame_bytes KN_CID) Hnn) as Hse.
  pose proof ASAN_CEIL_range as [CR _].
  destruct Hb as [(H1 & H2) | [(b & mm & Hbm & Hr) | [(Hi & Hns & He) | (cid & pos & Hin & Hr)]]].
  - split; [split; [lia | right; lia] |]. intros Hs. pose proof (proj1 (Hlow a HAR1 Hin1 Hs)). lia.
  - assert (Hb1 : In (b, mm) (ablocks B (k_lyc cx) S1)) by (rewrite Eab1; exact Hbm).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb1) as (_ & H4096 & Hbc & Hbapp & Hpo & _ & _).
    pose proof (in_app_addr _ _ a Hbapp Hr) as Hap. unfold app_addr, kLowShadowBeg, ASAN_CEIL in Hap.
    split; [split; lia|].
    intros [Hs | [Hs | Hs]].
    + pose proof (sep_block_frame SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 b mm KN_CID fpos HAR1 Hb1 Hin1) as Hd.
      unfold zdisjoint, in_zr, frame_rng in Hd, Hs. cbn [fst snd] in Hd, Hs. lia.
    + unfold in_zr in Hs. cbn [fst snd] in Hs. lia.
    + exact (proj2 (Hpo a Hr) (eq_ind_r (fun x => aowned B (k_lyc cx) S1 x) Hfo Hs)).
  - pose proof (pa_segs_low a Hi) as Hal. split; [split; lia|].
    intros Hs. exact (proj2 (Hlow a HAR1 Hin1 Hs) Hi).
  - assert (Hin' : In (cid, pos) (frames S1)) by (rewrite Hfrs1; right; exact Hin).
    destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 cid pos HAR1 Hin') as (Hf4' & Hfc' & Happ').
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (in_app_addr _ _ a Happ' Hr) as Hap. unfold app_addr, kLowShadowBeg, ASAN_CEIL in Hap.
    split; [split; lia|].
    intros Hs.
    apply in_split in Hin as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 (KN_CID, fpos) (cid, pos) [] l2 l3 HAR1
      ltac:(rewrite Hfrs1, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
    destruct (al_frames _ _ LAWS (k_lyc cx) S1 W1 mem1 md1 cid pos HAR1 Hin') as (_ & _ & Hfb' & _).
    destruct Hs as [Hs | [Hs | Hs]]; unfold in_zr, frame_rng in Hs; cbn [fst snd] in Hs.
    + lia.
    + lia.
    + subst a. exact (proj2 (Hfb' _ Hr) Hfo).
Qed.

Lemma at_cur : forall x, ka0 cx <= x < ka0 cx + 16 ->
  akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) x.
Proof. intros x Hx. pose proof HB as (_ & HRD & _). apply HRD. left. unfold ka0 in Hx. exact Hx. Qed.

Lemma at_in : forall x, k_wp cx <= x < k_wp cx + k_wn cx ->
  akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) x.
Proof.
  intros x Hx. pose proof HB as (_ & HRD & _ & _ & _ & HWP & HWN & HWPr & HWNr & _). apply HRD.
  right; left. exists (k_wp cx), (k_wn cx).
  split; [exact HWP|]. split; [exact HWN|]. split; [exact HWPr|]. split; [exact HWNr | lia].
Qed.

Lemma at_txb : forall x, LA_TEXTS <= x < LA_TEXTS + 8 * TEXTS_N ->
  akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) x.
Proof.
  intros x Hx. pose proof HB as (_ & HRD & _). apply HRD. right; right; right; right; right; left. exact Hx.
Qed.

(* kernel_apre's facts the phase uses *)
Lemma at_pre :
  apart_frame (k_regs cx) KERNEL_AK (ka0 cx) 16 /\ apart_gnl LA_G_NL (ka0 cx) 16 /\
  apart (ka0 cx) 16 LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3) /\
  range_addressable (ard SEGS (km0 cx)) SHADOW_OFF (ka0 cx) 16 /\
  amem_range (k_wp cx) (k_wn cx) /\ range_addressable (ard SEGS (km0 cx)) SHADOW_OFF (k_wp cx) (k_wn cx) /\
  kernel_apart (k_regs cx) (k_wp cx) (k_wn cx) /\
  range_addressable (ard SEGS (km0 cx)) SHADOW_OFF LA_TEXTS (8 * TEXTS_N) /\
  kernel_apart (k_regs cx) LA_TEXTS (8 * TEXTS_N) /\
  (forall i, 0 <= i < TEXTS_N ->
     exists p, au64_at SEGS (km0 cx) (LA_TEXTS + 8 * i) p /\ kernel_str SEGS (k_regs cx) (km0 cx) p) /\
  kernel_str SEGS (k_regs cx) (km0 cx) LA_STR_EMPTY.
Proof.
  pose proof HB as (_ & _ & HKP & _ & _ & HWP & HWN & HWPr & HWNr & _).
  destruct HKP as (kbs' & _ & _ & _ & _ & (wp' & wn' & HP1 & HN1 & HP1r & HN1r & _ & HAMR & HRAi & _ & HAPi) &
    _ & HRAc & HAPF & HAPG & HAPL & _ & _ & _ & _ & _ & _ & HRAT & HKAT & HTX & HSE & _).
  assert (Ep : wp' = k_wp cx).
  { pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HP1 HP1r) as R1.
    pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWP HWPr) as R2.
    unfold ka0 in R2. congruence. }
  assert (En : wn' = k_wn cx).
  { pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HN1 HN1r) as R1.
    pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWN HWNr) as R2.
    unfold ka0 in R2. congruence. }
  subst wp' wn'.
  split; [exact HAPF|]. split; [exact HAPG|]. split; [exact HAPL|]. split; [exact HRAc|].
  split; [exact HAMR|]. split; [exact HRAi|]. split; [exact HAPi|].
  split; [exact HRAT|]. split; [exact HKAT|]. split; [exact HTX | exact HSE].
Qed.

Lemma at_kE : forall x, kE cx x ->
  (0 <= x < 2 ^ 47 /\ (x < kLowMemEnd \/ kHighMemBeg <= x)) /\ (ka0 cx <= x < ka0 cx + 16 \/ x < kLowMemEnd).
Proof.
  intros x (r & Hr & Hx). pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold kernel_awr in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hx.
  - unfold LA_G_NL, NK_CHUNK, NK_OPEN in Hx. split; [split; lia | right; lia].
  - unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in Hx. split; [split; lia | right; lia].
  - change (aarg (k_regs cx) 0) with (ka0 cx) in Hx.
    split; [exact (proj1 (at_akb x (at_cur x Hx))) | left; exact Hx].
Qed.

Lemma at_fmiss : fmiss (k_lyc cx) (k_Sc cx) (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a).
Proof.
  apply fmiss_or.
  - apply (fmiss_app SEGS B LAWS (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) (kE cx) at_AR0).
    intros a Ha. exact (proj2 (proj1 (at_kE a Ha))).
  - pose proof HK as (_ & _ & _ & _ & _ & _ & _ & Hjbk & _).
    destruct Hjbk as (_ & _ & _ & Hnin & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & _) & _).
    assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
    pose proof HAR1 as (M1 & _).
    destruct (frame_facts B (k_lyc cx) S1 _ KN_CID fpos M1 Hin1) as (Cc & Cp & _).
    eapply fmiss_side; [exact at_AR0 | exact Cc | exact Cp | exact Hnin].
Qed.

Lemma at_saddr_now : forall x, akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) x ->
  saddr (aview SEGS (w_H (k_W cx)) (k_memc cx)) x -> saddr (aview SEGS (w_H W3) (ms_mem ms3)) x.
Proof.
  intros x Hx Hs. pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & (Kak & _) & _).
  destruct at_row as (Elo & Ehi).
  exact (kh_saddr_move B LAWS TB (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) ly3 S3 W3 (ms_mem ms3) md3
    (ksp cx - KERNEL_AK) (ksp cx) _ x at_AR0 at_AR3 Elo Ehi at_blocks Kak at_fmiss Hx Hs).
Qed.

Lemma at_ra_cur : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (ka0 cx) 16.
Proof.
  destruct at_pre as (_ & _ & _ & HRAc & _).
  intros x Hx. exact (at_saddr_now x (at_cur x Hx) (HRAc x Hx)).
Qed.

Lemma at_ra_tx : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF LA_TEXTS (8 * TEXTS_N).
Proof.
  destruct at_pre as (_ & _ & _ & _ & _ & _ & _ & HRAT & _).
  intros x Hx. exact (at_saddr_now x (at_txb x Hx) (HRAT x Hx)).
Qed.

Lemma at_sb : adv < k_wn cx -> exists s,
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s /\
  saddr_ok (k_wp cx + adv) s.
Proof.
  intros Hadv. pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  destruct at_pre as (_ & _ & _ & _ & _ & HRAi & _).
  exact (at_saddr_now (k_wp cx + adv) (at_in (k_wp cx + adv) ltac:(lia)) (HRAi (k_wp cx + adv) ltac:(lia))).
Qed.

(* a read-set byte's view at the current state is the entry's, when it is not a byte of kernel's writes *)
Lemma at_view_now : forall x, akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) x -> ~ kE cx x ->
  aview SEGS (w_H W3) (ms_mem ms3) x = aview SEGS (w_H (k_W cx)) (k_memc cx) x.
Proof.
  intros x Hx HnE.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & (Kak & _) & _).
  pose proof HB as ((HJ0 & _) & _).
  apply (akept_akb_gx SK SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
    (k_W0 cx) (k_mem0 cx) (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) (k_k cx)
    W3 (ms_mem ms3) (ksp cx - KERNEL_AK) (ksp cx) _ x HJ0 Kak Hx).
  intros [HE | HS]; [exact (HnE HE) | exact (proj2 (at_akb x Hx) HS)].
Qed.

Lemma at_db : adv < k_wn cx -> exists b, mbyte SEGS (rdW W3 (ms_mem ms3)) (k_wp cx + adv) = Some b.
Proof.
  intros Hadv.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HD & HDL & _).
  destruct at_pre as (_ & _ & _ & _ & _ & _ & (_ & HAPG & HAPL & HAPC) & _).
  unfold apart_gnl, apart in HAPG, HAPL, HAPC.
  destruct HD as (_ & _ & HD).
  assert (Hi : (Z.to_nat adv < length (k_d cx))%nat) by lia.
  destruct (nth_error (k_d cx) (Z.to_nat adv)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  exists b. pose proof (HD (Z.to_nat adv) Hi) as Hm. rewrite Eb, Z2Nat.id in Hm by lia.
  rewrite <- Hm. apply (mbyte_of_aview SEGS (w_H (k_W cx)) (w_H W3) (k_memc cx) (ms_mem ms3) (k_wp cx + adv)).
  apply at_view_now; [exact (at_in (k_wp cx + adv) ltac:(lia))|].
  intros (r & Hr & Hx). unfold kernel_awr in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hx.
  - unfold NK_CHUNK, NK_OPEN, NK_SIZE in Hx, HAPG. lia.
  - unfold LONG_ALIAS_SIZE in Hx, HAPL. lia.
  - lia.
Qed.

Lemma at_awr_cur : forall a, ka0 cx <= a < ka0 cx + 16 ->
  (awr_byte (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3
     ((KN_CID, fpos) :: k_own cx) a /\ ~ (k_sp0 cx <= a < k_sp0 cx + k_XO cx)) \/
  inG (k_G cx) a \/ (inFP (k_OUT cx) a /\ k_sp0 cx <= a < k_sp0 cx + k_XO cx).
Proof.
  intros a Ha.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & Hperm & _) & _).
  assert (HE : inFP (kernel_awr (k_regs cx) (km0 cx)) a).
  { exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16). split; [unfold kernel_awr; at_inl |].
    cbn [fst snd]. unfold ka0 in Ha. lia. }
  destruct (Hajw a HE) as [[Haw Hnout] | [HGa | Hout]]; [left; split; [|exact Hnout] | right; left; exact HGa |
    right; right; exact Hout].
  destruct Haw as [Hw | [(Hfp & b0 & n0 & Hbn & Hr) | [(b0 & n0 & Hbn & Hnb & Hr) | (cid & pos & Hown & Hr)]]].
  - left. exact Hw.
  - right; left. split; [exact Hfp|]. exists b0, n0. split; [|exact Hr].
    exact (Permutation_in _ (Permutation_sym Hperm) Hbn).
  - right; right; left. exists b0, n0. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hbn)|].
    split; [exact Hnb | exact Hr].
  - right; right; right. exists cid, pos. split; [right; exact Hown|]. rewrite at_fa. exact Hr.
Qed.

(* THE LANDING: a state whose memory differs from ms3's only at the cursor's 16 bytes; kernel_kit.v's frame lemmas
   carry every clause of kat but the cursor's and the cut's own registers *)
Lemma at_land : forall (ms' : machine_state) md' pc' adv' rl',
  kms pc' ms' ->
  (forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) hd_keepz = true -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  kregs_eq ms' rl' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  0 <= adv' <= k_wn cx ->
  au64_at SEGS (rdW W3 (ms_mem ms')) (ka0 cx) (k_wp cx + adv') ->
  au64_at SEGS (rdW W3 (ms_mem ms')) (ka0 cx + 8) (k_wn cx - adv') ->
  kat B cx fpos pc' (at_rl rl') at_sl (kfsh 0xf8 0 0xf3) true adv' (Some j) k2 ly3 S3 W3 ms' md' /\
  kw_at W3 ms' (kW2 cx fpos) n f.
Proof.
  intros ms' md' pc' adv' rl' Hkms HR Hrl UN HP Hfd Hfs Hadv' Hp' Hn'.
  set (X := fun a => ka0 cx <= a < ka0 cx + 16).
  pose proof HK as (_ & Hkr0 & Hkre & Hksv & Hkfr & Hksh & Hksl & Hkjbk & Hkkept & Hkcur & Hkg & Hkla).
  destruct at_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & HKA).
  destruct at_pre as (HAPF & HAPG & HAPL & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold apart_frame, apart_gnl, apart in HAPF, HAPG, HAPL.
  change (spZ (k_regs cx)) with (ksp cx) in HAPF. rewrite HKA in HAPF.
  pose proof Hkjbk as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & Hfr1 & _) & _).
  assert (HinF : In (KN_CID, fpos) (frames S1)) by (rewrite Hfr1; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR1 HinF) as (Hfa0 & Hfa1 & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  assert (HFb : 4096 <= kF cx fpos /\ kF cx fpos + 16384 <= alloc_ceiling) by (unfold kF; lia).
  assert (HFSH : SHADOW_OFF + 512 <= kFSH cx fpos /\ kFSH cx fpos + 0x448 <= 0x10007fff8000)
    by (unfold kFSH, shadow_of_addr; unfold SHADOW_OFF; lia).
  assert (CA : forall x, ka0 cx <= x < ka0 cx + 16 ->
            (0 <= x < 2 ^ 47 /\ (x < kLowMemEnd \/ kHighMemBeg <= x)) /\ ~ aside_rng (k_lyc cx) KN_CID fpos x)
    by (intros x Hx; exact (at_akb x (at_cur x Hx))).
  assert (FNC : forall a, kF cx fpos <= a < kF cx fpos + 16384 -> ~ (ka0 cx <= a < ka0 cx + 16)).
  { intros a Ha Hc. apply (proj2 (CA a Hc)). left. unfold in_zr, frame_rng. cbn [fst snd].
    unfold kF in Ha. rewrite Hfb. lia. }
  assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ X a ->
            aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) by exact UN.
  assert (Msv : forall a, ksp cx - 104 <= a < ksp cx -> ~ X a) by (intros a Ha Hc; unfold X in Hc; lia).
  assert (Mhd : forall a, kF cx fpos <= a < kF cx fpos + 24 -> ~ X a)
    by (intros a Ha Hc; exact (FNC a ltac:(lia) Hc)).
  assert (Mfl : forall a, kF cx fpos + fs_frame_bytes KN_CID - 8 <= a < kF cx fpos + fs_frame_bytes KN_CID -> ~ X a)
    by (intros a Ha Hc; rewrite Hfb in Ha; exact (FNC a ltac:(lia) Hc)).
  assert (Hl : Z.of_nat (length (kfsh 0xf8 0 0xf3)) = 0x448) by (rewrite kfsh_length; reflexivity).
  assert (Msh : forall a, kFSH cx fpos <= a < kFSH cx fpos + Z.of_nat (length (kfsh 0xf8 0 0xf3)) -> ~ X a).
  { rewrite Hl. intros a Ha Hc.
    destruct (CA a Hc) as ((_ & [Hq | Hq]) & _); rewrite ?C3, ?C5 in Hq; unfold SHADOW_OFF in HFSH; lia. }
  pose proof (kslots_okb_spec at_sl eq_refl) as SOK.
  assert (Msl : forall ov, In ov at_sl -> (0 <= fst ov <= 0xf0) /\
            (forall a, ksp1 cx + fst ov <= a < ksp1 cx + fst ov + 8 -> ~ X a)).
  { intros ov Hov. pose proof (SOK ov Hov) as S1'. split; [exact S1'|]. intros a Ha Hc. unfold X in Hc. lia. }
  assert (Mgn : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a).
  { intros a Ha Hc. unfold X in Hc. unfold LA_G_NL, NK_SIZE in *. lia. }
  assert (Mla : forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + LONG_ALIAS_SIZE -> ~ X a).
  { intros a Ha Hc. unfold X in Hc. unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in *. lia. }
  assert (HXin : forall a, X a -> kX_in cx fpos a).
  { intros a HXa. unfold kX_in. left. unfold kE, inFP. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
    split; [unfold kernel_awr; at_inl | cbn [fst snd]; unfold X, ka0 in HXa; lia]. }
  pose proof (kfsh_fits 0xf8 0 0xf3) as Hfits.
  pose proof (kk_grows_of_apresent _ _ _ _ HP) as HG.
  split.
  - unfold kat.
    refine (conj Hkms (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
    + (* kregs0 *)
      unfold kregs0 in Hkr0 |- *.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); rewrite HR by (vm_compute; reflexivity);
        tauto.
    + (* kregs_eq *)
      unfold kregs_eq, at_rl in Hkre |- *. rewrite !Forall_cons_iff in Hkre.
      destruct Hkre as (R19 & R21 & R24 & R25 & R22 & _). cbn [fst snd] in R19, R21, R24, R25, R22.
      apply Forall_cons; [cbn [fst snd]; rewrite HR by (vm_compute; reflexivity); exact R19|].
      apply Forall_cons; [cbn [fst snd]; rewrite HR by (vm_compute; reflexivity); exact R21|].
      apply Forall_cons; [cbn [fst snd]; rewrite HR by (vm_compute; reflexivity); exact R24|].
      apply Forall_cons; [cbn [fst snd]; rewrite HR by (vm_compute; reflexivity); exact R25|].
      apply Forall_cons; [cbn [fst snd]; rewrite HR by (vm_compute; reflexivity); exact R22|].
      exact Hrl.
    + eapply ksaved_frame with (X := X); eassumption.
    + eapply kframe_frame with (X := X); eassumption.
    + eapply kshadow_frame with (X := X); eassumption.
    + eapply kslots_frame with (X := X) (sl := at_sl); try apply incl_refl; eassumption.
    + eapply kjbk_md; eassumption.
    + eapply kkept_frame with (X := X); eassumption.
    + destruct Hkcur as (_ & _ & _ & HCW).
      split; [exact Hadv'|]. split; [exact Hp'|]. split; [exact Hn'|].
      intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (HCW i Hi)).
    + eapply kgnl_frame with (X := X); eassumption.
    + eapply kla_frame with (X := X); eassumption.
  - apply (kn_kw_keep W3 ms3 ms' (kW2 cx fpos) n f HW); [|exact HP].
    intros i Hi. apply UN; [unfold kW2, KN_W2, NW_SIZE in *; lia|].
    apply FNC. unfold kW2, KN_W2, NW_SIZE in *. lia.
Qed.

(* the environments' atoms *)
Lemma at_Ef : forall p nv d s,
  ew (at_E1 ms3 p nv d s) 18%nat = w64 (ka0 cx) /\ ew (at_E1 ms3 p nv d s) 9%nat = w64 (ksp1 cx) /\
  ew (at_E1 ms3 p nv d s) 20%nat = w64 SHADOW_OFF /\ ew (at_E1 ms3 p nv d s) 32%nat = w64 p /\
  ew (at_E1 ms3 p nv d s) 33%nat = w64 nv /\ ew (at_E1 ms3 p nv d s) 34%nat = w64 d /\
  ew (at_E1 ms3 p nv d s) 35%nat = w64 (SHADOW_OFF + p / 8) /\ ew (at_E1 ms3 p nv d s) 36%nat = w64 s.
Proof.
  intros p nv d s. pose proof HK as (_ & Hkr0 & _).
  destruct Hkr0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  assert (ER : forall (jj : nat) (r : bv 5), Z.of_nat jj = bv_unsigned r -> ew (at_E1 ms3 p nv d s) jj = getr (ms_regs ms3) r)
    by (intros jj r Hj; exact (ew_Eimg_Ereg_nat _ _ jj r Hj)).
  assert (EXT : forall jj, (jj < 5)%nat -> ew (at_E1 ms3 p nv d s) (32 + jj) =
            nth jj [w64 p; w64 nv; w64 d; w64 (SHADOW_OFF + p / 8); w64 s] (Z_to_bv 64 0))
    by (intros jj Hj; unfold at_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  split; [rewrite (ER 18%nat 18%bv eq_refl); exact R18|].
  split; [rewrite (ER 9%nat 9%bv eq_refl); exact R9|].
  split; [rewrite (ER 20%nat 20%bv eq_refl); exact R20|].
  split; [exact (EXT 0%nat ltac:(lia))|]. split; [exact (EXT 1%nat ltac:(lia))|].
  split; [exact (EXT 2%nat ltac:(lia))|]. split; [exact (EXT 3%nat ltac:(lia))|].
  exact (EXT 4%nat ltac:(lia)).
Qed.

Lemma at_shok : forall p nv d s, sh_ok SEGS hd_Bx hd_SH (at_E1 ms3 p nv d s) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  intros p nv d s. destruct (at_Ef p nv d s) as (E18 & _ & E20 & _).
  pose proof (CAp := fun x Hx => proj1 (at_akb x (at_cur x Hx))).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (CAp (ka0 cx) ltac:(lia)) as (Ha0 & _). pose proof (CAp (ka0 cx + 15) ltac:(lia)) as (Ha15 & _).
  apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold hd_Bx.
  rewrite (U_atom _ 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom _ 18 (ka0 cx) E18) by lia.
  split.
  - rewrite <- (aview_rd_of SEGS). rewrite Z.add_0_r. replace (16 - 0) with 16 by lia. exact at_ra_cur.
  - intros a Ha. change (Z.min 0 16) with 0 in Ha. change (Z.max 0 16) with 16 in Ha.
    destruct (CAp a ltac:(lia)) as (_ & [Hq | Hq]); unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

Lemma at_awr1 : forall E, base_val E (Some 18%nat) = ka0 cx ->
  awr_ok_x E at_rs1 (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx))
    (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros E BV18. unfold at_rs1.
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]]]].
  - intros x Hx. unfold hd_cur in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV18 in Hx.
    apply at_awr_cur. lia.
  - intros x Hx. unfold at_slots in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
  - intros x Hx. unfold hd_in in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
  - intros x Hx. unfold hd_ish in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
Qed.

Lemma at_awr0 : forall E,
  awr_ok_x E at_rs0 (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx))
    (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros E. unfold at_rs0. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros x Hx. unfold hd_cur in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
Qed.

Lemma at_awr2 : forall E,
  awr_ok_x E at_rs2 (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx))
    (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros E. unfold at_rs2. apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  - intros x Hx. unfold at_mg in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
  - intros x Hx. unfold at_tx in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
Qed.

(* the regs and slot facts at the cut *)
Lemma at_regs3 :
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 19)) = w64 (ka0 cx + 8) /\
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 24)) = w64 (kS8 cx) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp1 cx + KS_CSH) = Some (shadow_of_addr SHADOW_OFF (ka0 cx)).
Proof.
  pose proof HK as (_ & _ & Hkre & _ & _ & _ & Hksl & _).
  unfold kregs_eq, at_rl in Hkre. rewrite !Forall_cons_iff in Hkre.
  destruct Hkre as (R19 & R21 & R24 & R25 & R22 & _). cbn [fst snd] in R19, R24.
  split; [exact R19|]. split; [exact R24|].
  unfold kslots_eq in Hksl. rewrite Forall_forall in Hksl.
  exact (Hksl (KS_CSH, shadow_of_addr SHADOW_OFF (ka0 cx)) ltac:(unfold at_sl; apply in_or_app; left;
    unfold kslots_setup; at_inl)).
Qed.

(* THE STATE AT +0x9d8, n >= 1: the two cases of the input byte's shadow byte *)
Lemma at_seat1 : forall (fast : bool) s (b : byte),
  adv < k_wn cx ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s ->
  saddr_ok (k_wp cx + adv) s ->
  mbyte SEGS (rdW W3 (ms_mem ms3)) (k_wp cx + adv) = Some b ->
  (if fast then s = 0 else s <> 0) ->
  st_ok_pi SEGS pa_val (at_E1 ms3 (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned b) s) (at_ss1 fast)
    (restrict (w_H W3) ms3).
Proof.
  intros fast s b Hadv Hs Hsok Hb Hf.
  pose proof HK as (Hkms & Hkr0 & _ & _ & _ & _ & _ & _ & _ & Hkcur & _ & _).
  destruct Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  destruct at_regs3 as (R19 & R24 & SL_CSH).
  pose proof (kh_rdword_range _ _ _ _ SL_CSH) as Rg_CSH.
  destruct Hkcur as (Hadv0 & HCP & HCN & HCW).
  destruct at_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & HKA).
  destruct at_pre as (HAPF & _ & _ & _ & HAMR & _ & (HAPFi & _ & _ & HAPCi) & _).
  unfold apart_frame, apart in HAPF, HAPFi, HAPCi. unfold amem_range in HAMR.
  change (spZ (k_regs cx)) with (ksp cx) in HAPF, HAPFi.
  change (aarg (k_regs cx) 0) with (ka0 cx) in HAPF, HAPCi. rewrite HKA in HAPF, HAPFi.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (CAp := fun x Hx => proj1 (at_akb x (at_cur x Hx))).
  pose proof (CAp (ka0 cx) ltac:(lia)) as (Ha0 & Hc0). pose proof (CAp (ka0 cx + 15) ltac:(lia)) as (Ha15 & Hc15).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  unfold aview in Hs.
  destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)))
    as [bs|] eqn:Ebs; [|discriminate Hs].
  cbn [option_map] in Hs. injection Hs as Hs.
  assert (Hsr : 0 <= s < 8) by (pose proof (bv_unsigned_in_range 8 bs); unfold saddr_ok in Hsok; lia).
  destruct (at_Ef (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned b) s)
    as (E18 & E9 & E20 & E32 & E33 & E34 & E35 & E36).
  remember (at_E1 ms3 (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned b) s) as E eqn:HEdef.
  assert (BV : forall nn v, ew E nn = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
  { intros nn v Hn Hv. cbn [base_val]. rewrite Hn. unfold w64. apply unsigned_lit_small. exact Hv. }
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv + 1 <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemEnd in HAMR; lia).
  pose proof (BV 18%nat (ka0 cx) E18 ltac:(lia)) as BV18. pose proof (BV 9%nat (ksp1 cx) E9 ltac:(lia)) as BV9.
  pose proof (BV 32%nat (k_wp cx + adv) E32 ltac:(lia)) as BV32.
  assert (Hq : SHADOW_OFF <= SHADOW_OFF + (k_wp cx + adv) / 8 < SHADOW_OFF + 2 ^ 44)
    by (split; [pose proof (Z.div_pos (k_wp cx + adv) 8 ltac:(lia) ltac:(lia)); lia |
                pose proof (Z.div_lt_upper_bound (k_wp cx + adv) 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia]).
  pose proof (BV 35%nat (SHADOW_OFF + (k_wp cx + adv) / 8) E35 ltac:(unfold SHADOW_OFF in *; lia)) as BV35.
  rewrite (kh_ms_shape ms3 (BASE + kpc KP_ATTR) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  assert (HS0 : st_ok_pi SEGS pa_val E (mkSS (kpc KP_ATTR) sr_atoms at_rs1 None
                 (mkFacts hd_atoms (at_cs fast) hd_alias))
                 (mkst (ms_regs ms3) (w64 (BASE + kpc KP_ATTR)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - rewrite HEdef. unfold at_E1. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold at_rs1. repeat apply Forall_cons; [..|apply Forall_nil].
      + unfold hd_cur, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV18. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HCW o Ho)|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 32 0) (k_wp cx + adv));
            [apply sv_off0; exact E32 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HCP].
        * apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 (SOff 33 0) (k_wn cx - adv));
            [apply sv_off0; exact E33 | cbn; lia | cbn; lia | exact HCN].
      + unfold at_slots, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (kh_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc0 (hd_sh 18 0) (shadow_of_addr SHADOW_OFF (ka0 cx)));
          [|exact SL_CSH].
        rewrite (kh_denot_sh E 18 (ka0 cx) 0 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
        rewrite Z.add_0_r. reflexivity.
      + unfold hd_in, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (k_wp cx + adv) 0 1 (SOff 34 0) (bv_unsigned b));
          [apply sv_off0; exact E34 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact (kh_val1 _ _ _ Hb)].
      + unfold hd_ish, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV35. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
        split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (SHADOW_OFF + (k_wp cx + adv) / 8) 0 1 (SOff 36 0) s);
          [apply sv_off0; exact E36 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r, <- Hs. exact (kh_val1 _ _ _ Ebs).
    - apply pairwise_disjoint_of_extents.
      unfold at_rs1, hd_cur, at_slots, hd_in, hd_ish, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV18, BV9, BV32, BV35.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hadv Hadv0 HAPF HAPFi HAPCi HAMR Hc0 Hc15 Ha0 Ha15 Hp64 Hq G1 G2 G3 G4 G5 G6 G7 C1a C3 C5.
      unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *.
      repeat split; lia.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
      + unfold hd_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E18, E9, E20, E34, E36. unfold w64.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
        change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
        unfold SHADOW_OFF.
        repeat split; first [lia | exact G8 | exact I].
      + assert (D33 : sv_denot E (SOff 33 0) = Z_to_bv 64 (k_wn cx - adv)) by (apply sv_off0; exact E33).
        assert (D36 : sv_denot E (SOff 36 0) = Z_to_bv 64 s) by (apply sv_off0; exact E36).
        assert (D0 : sv_denot E (SLit 0) = Z_to_bv 64 0) by reflexivity.
        assert (Dslow : sv_denot E (SAlu ALU_AND (SOff 32 0) (SLit 7)) = Z_to_bv 64 ((k_wp cx + adv) mod 8)).
        { rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
          rewrite (U_atom_off E 32 (k_wp cx + adv) 0 E32 ltac:(lia) ltac:(lia)), Z.add_0_r.
          change (zcanon 7) with 7.
          assert (Hl7 : Z.land (k_wp cx + adv) 7 = (k_wp cx + adv) mod 8)
            by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
          rewrite Hl7. apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound (k_wp cx + adv) 8). lia. }
        assert (BEQ : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
                  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y)).
        { intros x y Hx Hy. unfold branch_taken, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. }
        assert (BNE : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
                  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y)).
        { intros x y Hx Hy. change BC_NE with (neg_bc BC_EQ). rewrite branch_taken_neg, BEQ by assumption.
          reflexivity. }
        pose proof (Z.mod_pos_bound (k_wp cx + adv) 8 ltac:(lia)) as Hm8.
        destruct fast; cbv iota in Hf; unfold at_cs; cbn [conds_ok]; unfold acond_ok;
          cbn [ac_c ac_a ac_b];
          rewrite ?D33, ?D36, ?D0, ?Dslow;
          repeat match goal with |- _ /\ _ => split end;
          try exact I;
          first [ rewrite BNE by lia; apply negb_true_iff, Z.eqb_neq; lia
                | rewrite BEQ by lia; apply Z.eqb_eq; lia
                | apply kh_blt; unfold saddr_ok in Hsok; lia ].
      + unfold hd_alias. cbn [alias_ok]. split; [|exact I].
        rewrite (kh_denot_sh E 32 (k_wp cx + adv) 0 E32 ltac:(lia) ltac:(lia) ltac:(lia) E20).
        rewrite (sv_off0 E 35 _ E35). rewrite Z.add_0_r. reflexivity. }
  assert (HD19 : sv_denot E (SOff 18 8) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 19))).
  { rewrite R19. cbn [sv_denot]. rewrite E18. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (HD24 : sv_denot E (hd_sh 18 8) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 24))).
  { rewrite R24, (kh_denot_sh E 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
    unfold w64, kS8, shadow_of_addr. reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 (Z.of_nat 19)) (SOff 18 8) HS0 eq_refl HD19) as HS1.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 (Z.of_nat 24)) (hd_sh 18 8) HS1 eq_refl HD24) as HS2.
  exact HS2.
Qed.

(* THE STATE AT +0x9d8, n = 0 *)
Lemma at_seat0 : k_wn cx - adv = 0 ->
  st_ok_pi SEGS pa_val (at_E1 ms3 (k_wp cx + adv) 0 0 0) at_ss0 (restrict (w_H W3) ms3).
Proof.
  intros Hn0.
  pose proof HK as (Hkms & Hkr0 & _ & _ & _ & _ & _ & _ & _ & Hkcur & _ & _).
  destruct Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  destruct at_regs3 as (R19 & R24 & _).
  destruct Hkcur as (Hadv0 & HCP & HCN & HCW). rewrite Hn0 in HCN.
  destruct at_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & HKA).
  destruct at_pre as (_ & _ & _ & _ & HAMR & _). unfold amem_range in HAMR.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (CAp := fun x Hx => proj1 (at_akb x (at_cur x Hx))).
  pose proof (CAp (ka0 cx) ltac:(lia)) as (Ha0 & _). pose proof (CAp (ka0 cx + 15) ltac:(lia)) as (Ha15 & _).
  destruct (at_Ef (k_wp cx + adv) 0 0 0) as (E18 & E9 & E20 & E32 & E33 & E34 & E35 & E36).
  remember (at_E1 ms3 (k_wp cx + adv) 0 0 0) as E eqn:HEdef.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  assert (Hp64 : 0 <= k_wp cx + adv <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemEnd in HAMR; lia).
  assert (BV18 : base_val E (Some 18%nat) = ka0 cx).
  { cbn [base_val]. rewrite E18. unfold w64. apply unsigned_lit_small. lia. }
  rewrite (kh_ms_shape ms3 (BASE + kpc KP_ATTR) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  assert (HS0 : st_ok_pi SEGS pa_val E (mkSS (kpc KP_ATTR) sr_atoms at_rs0 None (mkFacts hd_atoms [] hd_alias))
                 (mkst (ms_regs ms3) (w64 (BASE + kpc KP_ATTR)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - rewrite HEdef. unfold at_E1. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold at_rs0. apply Forall_cons; [|apply Forall_nil].
      unfold hd_cur, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite BV18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 32 0) (k_wp cx + adv));
          [apply sv_off0; exact E32 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HCP].
      + apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact HCN].
    - unfold at_rs0. cbn [pairwise_disjoint all_disjoint]. tauto.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
      + unfold hd_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E18, E9, E20, E34, E36. unfold w64.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
        change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
        unfold SHADOW_OFF.
        repeat split; first [lia | exact G8 | exact I].
      + exact I.
      + unfold hd_alias. cbn [alias_ok]. split; [|exact I].
        rewrite (kh_denot_sh E 32 (k_wp cx + adv) 0 E32 ltac:(lia) ltac:(lia) ltac:(lia) E20).
        rewrite (sv_off0 E 35 _ E35). rewrite Z.add_0_r. reflexivity. }
  assert (HD19 : sv_denot E (SOff 18 8) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 19))).
  { rewrite R19. cbn [sv_denot]. rewrite E18. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (HD24 : sv_denot E (hd_sh 18 8) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 24))).
  { rewrite R24, (kh_denot_sh E 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
    unfold w64, kS8, shadow_of_addr. reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 (Z.of_nat 19)) (SOff 18 8) HS0 eq_refl HD19) as HS1.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 (Z.of_nat 24)) (hd_sh 18 8) HS1 eq_refl HD24) as HS2.
  exact HS2.
Qed.

(* the read-only view at a state whose memory is ms3's but at the cursor (kernel's writes are never read-only) *)
Lemma at_ro_move : forall (ms' : machine_state),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) (ms_mem ms')).
Proof.
  intros ms' UN.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & Kro) & _).
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWRO) & _).
  intros a Hro Hno Her.
  pose proof (kn_ro_low a Hro) as Hlow.
  assert (Hnc : ~ (ka0 cx <= a < ka0 cx + 16)).
  { intros Hc. apply (HWRO a); [|exact Hro]. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
    split; [unfold kernel_awr; at_inl | cbn [fst snd]; unfold ka0 in Hc; lia]. }
  rewrite (UN a ltac:(lia) Hnc). exact (Kro a Hro Hno Her).
Qed.

(* THE STATE AT +0xa30 (stage 2), over a machine state msA that stage 1 reached: s7 = d, s4 = the shadow base;
   msA's memory is ms3's but at the cursor; T = texts + 8 * ((d / 8) mod 11) holds tp *)
Lemma at_seat2 : forall (msA : machine_state) d tp,
  ms_pc_val msA = w64 (BASE + kpc 0xa30) -> ms_resv msA = None -> ms_svc_pending msA = None ->
  ms_rom msA = seg_rom SEGS -> ms_fregs msA = fp_regs -> ms_fcsr msA = fp_csr ->
  getr (ms_regs msA) (Z_to_bv 5 23) = w64 d -> 0 <= d < 256 ->
  getr (ms_regs msA) (Z_to_bv 5 20) = w64 SHADOW_OFF ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  au64_at SEGS (km0 cx) (LA_TEXTS + 8 * ((d / 8) mod 11)) tp -> 0 <= tp < 2 ^ 64 ->
  st_ok_pi SEGS pa_val (at_E2 msA (LA_TEXTS + 8 * ((d / 8) mod 11)) tp) at_ss2 (restrict (w_H W3) msA) /\
  sh_ok SEGS hd_Bx at_SH2 (at_E2 msA (LA_TEXTS + 8 * ((d / 8) mod 11)) tp) (mrestrict (w_H W3) (ms_mem msA)).
Proof.
  intros msA d tp Hpc Hrv Hsvc Hrom Hfrg Hfcs R23 Hd R20 UNA HTP Htp.
  assert (HT : LA_TEXTS <= LA_TEXTS + 8 * ((d / 8) mod 11) /\
               LA_TEXTS + 8 * ((d / 8) mod 11) + 8 <= LA_TEXTS + 8 * TEXTS_N /\
               (LA_TEXTS + 8 * ((d / 8) mod 11)) mod 8 = 0).
  { pose proof (Z.mod_pos_bound (d / 8) 11 ltac:(lia)). unfold LA_TEXTS, TEXTS_N. split; [lia|].
    split; [lia|]. rewrite Z.add_mod, Z.mul_comm, Z_mod_mult, Z.add_0_r by lia. reflexivity. }
  set (T := LA_TEXTS + 8 * ((d / 8) mod 11)) in *.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct at_objs as (O8 & O18 & O19).
  destruct at_pre as (_ & _ & _ & _ & _ & _ & _ & HRAT & HKAT & _).
  destruct HKAT as (_ & HKG & HKL & HKC). unfold apart_gnl, apart in HKG, HKL, HKC.
  change (aarg (k_regs cx) 0) with (ka0 cx) in HKC.
  assert (TNC : forall x, LA_TEXTS <= x < LA_TEXTS + 8 * TEXTS_N -> ~ (ka0 cx <= x < ka0 cx + 16))
    by (intros x Hx Hc; unfold TEXTS_N in *; lia).
  assert (TNE : forall x, LA_TEXTS <= x < LA_TEXTS + 8 * TEXTS_N -> ~ kE cx x).
  { intros x Hx (r & Hr & Hxr). unfold kernel_awr in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hxr.
    - unfold NK_CHUNK, NK_OPEN, NK_SIZE, TEXTS_N in *. lia.
    - unfold LONG_ALIAS_SIZE, TEXTS_N in *. lia.
    - change (aarg (k_regs cx) 0) with (ka0 cx) in Hxr. exact (TNC x Hx Hxr). }
  (* the texts word at msA *)
  assert (HTPA : au64_at SEGS (rdW W3 (ms_mem msA)) T tp).
  { apply (val_mem_moved SEGS (w_H (k_W cx)) (w_H W3) (k_memc cx) (ms_mem msA) T T 8 tp); [|exact HTP].
    intros i Hi. cbn in Hi.
    assert (Hx : LA_TEXTS <= T + i < LA_TEXTS + 8 * TEXTS_N) by lia.
    rewrite (UNA (T + i) ltac:(unfold LA_TEXTS, TEXTS_N in *; lia) (TNC _ Hx)).
    exact (at_view_now (T + i) (at_txb _ Hx) (TNE _ Hx)). }
  (* the magic's word at msA *)
  pose proof (ki_m11_val_mem pa_segs PCAP_RLO PCAP_RHI B KI (w_H W3) (ms_mem msA) (at_ro_move msA UNA)) as HMG.
  (* the environment *)
  assert (EA : ew (at_E2 msA T tp) 23%nat = w64 d /\ ew (at_E2 msA T tp) 20%nat = w64 SHADOW_OFF /\
               ew (at_E2 msA T tp) 32%nat = w64 T /\ ew (at_E2 msA T tp) 33%nat = w64 tp /\
               ew (at_E2 msA T tp) (A_OBJ 18) = w64 KI_M11 /\ ew (at_E2 msA T tp) (A_OBJ 19) = w64 LA_TEXTS).
  { unfold at_E2.
    split; [rewrite (ew_Eimg_Ereg_nat _ _ 23 (Z_to_bv 5 23) eq_refl); exact R23|].
    split; [rewrite (ew_Eimg_Ereg_nat _ _ 20 (Z_to_bv 5 20) eq_refl); exact R20|].
    split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ [w64 T; w64 tp] 0)|].
    split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ [w64 T; w64 tp] 1)|].
    split; [rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite O18; reflexivity|].
    rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite O19; reflexivity. }
  destruct EA as (E23 & E20 & E32 & E33 & E18o & E19o).
  remember (at_E2 msA T tp) as E eqn:HEdef.
  assert (BV : forall nn v, ew E nn = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
  { intros nn v Hn Hv. cbn [base_val]. rewrite Hn. unfold w64. apply unsigned_lit_small. exact Hv. }
  assert (HTr : 0 <= T < 2 ^ 64) by (unfold LA_TEXTS, TEXTS_N in *; lia).
  pose proof (BV 32%nat T E32 HTr) as BV32.
  pose proof (BV (A_OBJ 18) KI_M11 E18o ltac:(unfold KI_M11; lia)) as BV18.
  split.
  - rewrite (kh_ms_shape msA (BASE + kpc 0xa30) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
    apply pa_entry_st_ok_full.
    + rewrite HEdef. unfold at_E2. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold at_rs2. repeat apply Forall_cons; [..|apply Forall_nil].
      * unfold at_mg, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV18. unfold KI_M11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ KI_M11 0 8 (SLit KI_M11_V) KI_M11_V);
          [reflexivity | cbn; unfold KI_M11_V; lia | cbn; lia | rewrite Z.add_0_r; exact HMG].
      * unfold at_tx, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ T 0 8 (SOff 33 0) tp);
          [apply sv_off0; exact E33 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HTPA].
    + apply pairwise_disjoint_of_extents.
      unfold at_rs2, at_mg, at_tx, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV18, BV32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold KI_M11, LA_TEXTS in *. repeat split; lia.
    + unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
      * unfold at_atoms2. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E23, E20, E32. unfold w64.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF, LA_TEXTS, TEXTS_N in *; lia).
        change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
        unfold SHADOW_OFF, LA_TEXTS, TEXTS_N in *.
        repeat split; first [lia | exact I].
      * exact I.
      * unfold at_alias2. cbn [alias_ok]. split; [|exact I].
        rewrite (sv_off0 E 32 _ E32). rewrite denot_lit_U. f_equal.
        rewrite U_SAlu. cbn [zalu_raw].
        rewrite (U_atom E (A_OBJ 19) LA_TEXTS E19o ltac:(unfold LA_TEXTS; lia)).
        rewrite (at_idx_U E d E23 Hd). apply zcanon_id. unfold M64. subst T. lia.
  - apply Forall_cons; [|apply Forall_nil].
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold hd_Bx.
    rewrite (U_atom _ 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
    rewrite (U_atom _ 32 T E32) by lia.
    split.
    + rewrite <- (aview_rd_of SEGS). rewrite Z.add_0_r. replace (8 - 0) with 8 by lia.
      intros x Hx.
      assert (Hx' : LA_TEXTS <= x < LA_TEXTS + 8 * TEXTS_N) by lia.
      destruct (at_ra_tx x Hx') as (sb & Hsb & Hok). exists sb. split; [|exact Hok].
      assert (Hsx : ~ (ka0 cx <= shadow_of_addr SHADOW_OFF x < ka0 cx + 16)).
      { intros Hc.
        pose proof (CAp := fun y Hy => proj1 (at_akb y (at_cur y Hy))).
        destruct (CAp _ Hc) as (_ & [Hq | Hq]); unfold shadow_of_addr, kLowMemEnd, kHighMemBeg, SHADOW_OFF in *;
          unfold LA_TEXTS, TEXTS_N in *; lia. }
      rewrite (UNA (shadow_of_addr SHADOW_OFF x) ltac:(unfold shadow_of_addr, SHADOW_OFF, LA_TEXTS, TEXTS_N in *; lia) Hsx).
      exact Hsb.
    + intros a Ha. change (Z.min 0 8) with 0 in Ha. change (Z.max 0 8) with 8 in Ha.
      unfold SHADOW_OFF, LA_TEXTS, TEXTS_N in *. lia.
Qed.

(* a cursor word of a run's end state, off its cursor region *)
Lemma at_curw : forall E (msF : machine_state) lo hi wlo whi cs off e v,
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem msF)) (YP09.mkRegion (Some 18%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 18%nat) = ka0 cx -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  au64_at SEGS (rdW W3 (ms_mem msF)) (ka0 cx + off) v.
Proof.
  intros E msF lo hi wlo whi cs off e v HR Hb Hin He Hv.
  exact (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) cs lo hi wlo whi off 8 e v HR Hb Hin He
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(change (Z.of_N 8) with 8; lia)).
Qed.

(* the run's writable windows: the cursor (stage 1), nothing (the empty cursor, stage 2) *)
Lemma at_win1 : forall E, base_val E (Some 18%nat) = ka0 cx ->
  forall bb wlo whi a, In (bb, wlo, whi) (windows at_rs1) -> base_val E bb + wlo <= a < base_val E bb + whi ->
  ka0 cx <= a < ka0 cx + 16.
Proof.
  intros E BV18 bb wlo whi a Hin Ha.
  assert (Hw : windows at_rs1 = [(Some 18%nat, 0, 16); (Some 9%nat, 192, 192); (Some 32%nat, 0, 0); (Some 35%nat, 0, 0)])
    by (vm_compute; reflexivity).
  rewrite Hw in Hin. cbn [In] in Hin.
  destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-.
  - rewrite BV18 in Ha. lia.
  - lia.
  - lia.
  - lia.
Qed.

Lemma at_win0 : forall E bb wlo whi a, In (bb, wlo, whi) (windows at_rs0) ->
  base_val E bb + wlo <= a < base_val E bb + whi -> ka0 cx <= a < ka0 cx + 16.
Proof.
  intros E bb wlo whi a Hin Ha.
  assert (Hw : windows at_rs0 = [(Some 18%nat, 0, 0)]) by (vm_compute; reflexivity).
  rewrite Hw in Hin. cbn [In] in Hin.
  destruct Hin as [Hq | []]; injection Hq as <- <- <-. lia.
Qed.

Lemma at_win2 : forall E bb wlo whi a, In (bb, wlo, whi) (windows at_rs2) ->
  base_val E bb + wlo <= a < base_val E bb + whi -> False.
Proof.
  intros E bb wlo whi a Hin Ha.
  assert (Hw : windows at_rs2 = [(Some (A_OBJ 18), 0, 0); (Some 32%nat, 0, 0)]) by (vm_compute; reflexivity).
  rewrite Hw in Hin. cbn [In] in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; lia.
Qed.

(* the machine state's shape at a run's end *)
Lemma at_kms : forall E ss' (msF : machine_state) pcF,
  st_ok_pi SEGS pa_val E ss' (restrict (w_H W3) msF) -> ss_resv ss' = None -> ss_pc ss' = kpc pcF -> kms pcF msF.
Proof.
  intros E ss' msF pcF HS Hrv Hpc.
  pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss' msF HS Hrv) as Hsh. rewrite Hpc in Hsh.
  unfold kms. rewrite Hsh. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
  repeat split; reflexivity.
Qed.

(* THE PHASE at this context *)
Lemma at_go : forall (Q : world SEGS -> config -> Prop),
  (forall ms' md', ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx)
       (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
     kat B cx fpos KP_A0 (at_rl [(23%nat, 0); (27%nat, LA_STR_EMPTY)]) at_sl (kfsh 0xf8 0 0xf3) true adv
       (Some j) k2 ly3 S3 W3 ms' md' ->
     kw_at W3 ms' (kW2 cx fpos) n f ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  (forall a p ms' md', 0 <= a < 256 -> au64_at SEGS (km0 cx) (LA_TEXTS + 8 * ((a / 8) mod 11)) p ->
     ktext cx p ->
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx)
       (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
     kat B cx fpos KP_TXT (at_rl [(23%nat, a); (27%nat, p)]) at_sl (kfsh 0xf8 0 0xf3) true (adv + 1)
       (Some j) k2 ly3 S3 W3 ms' md' ->
     kw_at W3 ms' (kW2 cx fpos) n f ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros Q CA0 CTXT.
  pose proof HB as ((HJ0 & HGok & _) & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  destruct at_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & HKA).
  destruct at_pre as (_ & _ & _ & _ & HAMR & _ & _ & _ & _ & HTX & HSE). unfold amem_range in HAMR.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (CAp := fun x Hx => proj1 (at_akb x (at_cur x Hx))).
  pose proof (CAp (ka0 cx) ltac:(lia)) as (Ha0 & _). pose proof (CAp (ka0 cx + 15) ltac:(lia)) as (Ha15 & _).
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemEnd in HAMR; lia).
  destruct at_objs as (O8 & O18 & O19).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  destruct (Z.eq_dec (k_wn cx - adv) 0) as [Hn0 | Hn1].
  - (* n = 0: +0x9d8 .. +0x9e8, +0xac8 .. +0xad4, j +0xb10; nothing written *)
    remember (at_E1 ms3 (k_wp cx + adv) 0 0 0) as E eqn:HEdef.
    assert (HS : st_ok_pi SEGS pa_val E at_ss0 (restrict (w_H W3) ms3)) by (rewrite HEdef; exact (at_seat0 Hn0)).
    assert (EF : ew E 18%nat = w64 (ka0 cx) /\ ew E 32%nat = w64 (k_wp cx + adv)).
    { rewrite HEdef. destruct (at_Ef (k_wp cx + adv) 0 0 0) as (E18 & _ & _ & E32 & _). tauto. }
    destruct EF as (E18 & E32).
    assert (E8o : ew E (A_OBJ 8) = w64 LA_STR_EMPTY)
      by (rewrite HEdef; unfold at_E1; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite O8;
          reflexivity).
    assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; unfold at_E1; apply Eimg_env).
    assert (BV18u : bv_unsigned (ew E 18%nat) = ka0 cx) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
    assert (SHOK : sh_ok SEGS hd_Bx hd_SH E (mrestrict (w_H W3) (ms_mem ms3))) by (rewrite HEdef; apply at_shok).
    pose proof HS as HS0. pose proof HJ3 as HJ.
    paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc KP_A0).
    { exact (at_awr0 E). }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mm) => rename mm into msF end.
    repeat rewrite wvb_collapse in HJ.
    spregion HS 0%nat HR0.
    prreg HS (Z_to_bv 5 23) R23. prreg HS (Z_to_bv 5 27) R27.
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
      pose proof (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem msF)
        (fun a => ka0 cx <= a < ka0 cx + 16) HFr (at_win0 E)) as UN;
      pose proof (fun a Hp => kh_apres_grows _ _ _ a HG Hp) as HP end.
    lazymatch goal with HJ' : ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdF _ |- SRr _ _ (mkCfg _ ?mdF) _ =>
      assert (Hmd : m_fds mdF = m_fds md3 /\ m_fs mdF = m_fs md3)
        by (split; [repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
                   | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity]) end.
    destruct (at_land msF _ KP_A0 adv [(23%nat, 0); (27%nat, LA_STR_EMPTY)]
      (at_kms E _ msF KP_A0 HS eq_refl ltac:(vm_compute; reflexivity))
      (kh_reg_same E _ _ (w_H W3) ms3 msF hd_keepz HS0 HS ltac:(vm_compute; reflexivity))
      ltac:(unfold kregs_eq; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
            try change (Z.of_nat 23) with 23; try change (Z.of_nat 27) with 27;
            [rewrite R23; reflexivity | rewrite R27; first [exact E8o | apply sv_off0; exact E8o]])
      UN HP (proj1 Hmd) (proj2 Hmd) ltac:(lia)
      ltac:(pose proof (at_curw E msF _ _ _ _ _ 0 (SOff 32 0) _ HR0 BV18u ltac:(at_inl) (sv_off0 E 32 _ E32)
              ltac:(lia)) as VP; rewrite Z.add_0_r in VP; exact VP)
      ltac:(rewrite Hn0; exact (at_curw E msF _ _ _ _ _ 8 (SLit 0) 0 HR0 BV18u ltac:(at_inl) eq_refl ltac:(lia))))
      as (HKF & HWF).
    exact (CA0 msF _ HJ HKF HWF).
  - (* n >= 1: stage 1 to +0xa30, stage 2 to +0xa74 *)
    assert (Hadv : adv < k_wn cx) by lia.
    destruct (at_sb Hadv) as (s & Hs & Hsok). destruct (at_db Hadv) as (b & Hb).
    pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
    set (d := bv_unsigned b) in *.
    destruct (HTX ((d / 8) mod 11) ltac:(pose proof (Z.mod_pos_bound (d / 8) 11 ltac:(lia)); unfold TEXTS_N; lia))
      as (tp & HTP & HKS).
    assert (Htp : 0 <= tp < 2 ^ 64).
    { destruct HKS as (sx & slx & _ & ((Hlo & Hhi & _) & _) & _). rewrite length_app in Hhi. cbn [length] in Hhi.
      lia. }
    assert (GO : forall (fast : bool), (if fast then s = 0 else s <> 0) -> SRr SEGS W3 (mkCfg ms3 md3) Q).
    { intros fast Hf. destruct fast.
      -
          remember (at_E1 ms3 (k_wp cx + adv) (k_wn cx - adv) d s) as E eqn:HEdef.
          assert (HS : st_ok_pi SEGS pa_val E (at_ss1 true) (restrict (w_H W3) ms3))
            by (rewrite HEdef; exact (at_seat1 true s b Hadv Hs Hsok Hb Hf)).
          assert (EF : ew E 18%nat = w64 (ka0 cx) /\ ew E 32%nat = w64 (k_wp cx + adv) /\
                       ew E 33%nat = w64 (k_wn cx - adv) /\ ew E 34%nat = w64 d).
          { rewrite HEdef. destruct (at_Ef (k_wp cx + adv) (k_wn cx - adv) d s)
              as (E18 & _ & _ & E32 & E33 & E34 & _). tauto. }
          destruct EF as (E18 & E32 & E33 & E34).
          assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; unfold at_E1; apply Eimg_env).
          assert (BV18u : bv_unsigned (ew E 18%nat) = ka0 cx) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
          assert (BV18 : base_val E (Some 18%nat) = ka0 cx) by (cbn [base_val]; exact BV18u).
          assert (SHOK : sh_ok SEGS hd_Bx hd_SH E (mrestrict (w_H W3) (ms_mem ms3))) by (rewrite HEdef; apply at_shok).
          assert (DP : sv_denot E (SOff 32 1) = Z_to_bv 64 (k_wp cx + (adv + 1))).
          { cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
          assert (DN : sv_denot E (SOff 33 (-1)) = Z_to_bv 64 (k_wn cx - (adv + 1))).
          { cbn [sv_denot]. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
          pose proof HS as HS0. pose proof HJ3 as HJ.
          (* stage 1 *)
          paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc 0xa30).
          { exact (at_awr1 E BV18). }
          lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mm) => rename mm into msA end.
          repeat rewrite wvb_collapse in HJ.
          spregion HS 0%nat HR0.
          prreg HS (Z_to_bv 5 23) R23A.
          pose proof (kh_reg_same E _ _ (w_H W3) ms3 msA hd_keepz HS0 HS ltac:(vm_compute; reflexivity)) as KR1.
          lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
            pose proof (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem msA)
              (fun a => ka0 cx <= a < ka0 cx + 16) HFr (at_win1 E BV18)) as UN1;
            pose proof (fun a Hp => kh_apres_grows _ _ _ a HG Hp) as HP1; clear HFr HG end.
          pose proof (at_curw E msA _ _ _ _ _ 0 (SOff 32 1) _ HR0 BV18u ltac:(at_inl) DP ltac:(lia)) as VPA.
          rewrite Z.add_0_r in VPA.
          pose proof (at_curw E msA _ _ _ _ _ 8 (SOff 33 (-1)) _ HR0 BV18u ltac:(at_inl) DN ltac:(lia)) as VNA.
          pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ msA HS eq_refl) as ShA.
          lazymatch type of ShA with msA = mkst _ (Z_to_bv 64 (_ + ss_pc ?ssx)) _ _ =>
            assert (PcA : ss_pc ssx = kpc 0xa30) by (vm_compute; reflexivity) end.
          rewrite PcA in ShA.
          assert (R23' : getr (ms_regs msA) (Z_to_bv 5 23) = w64 d) by (rewrite R23A; first [exact E34 | apply sv_off0; exact E34]).
          assert (R20' : getr (ms_regs msA) (Z_to_bv 5 20) = w64 SHADOW_OFF).
          { rewrite (KR1 (Z_to_bv 5 20) ltac:(vm_compute; reflexivity)).
            pose proof HK as (_ & (_ & _ & _ & _ & _ & _ & R20) & _). exact R20. }
          clear HS0.
          (* stage 2 *)
          destruct (at_seat2 msA d tp ltac:(rewrite ShA; reflexivity) ltac:(rewrite ShA; reflexivity)
            ltac:(rewrite ShA; reflexivity) ltac:(rewrite ShA; reflexivity) ltac:(rewrite ShA; reflexivity)
            ltac:(rewrite ShA; reflexivity) R23' Hbr R20' UN1 HTP Htp) as (HS2 & SHOK2).
          set (E2 := at_E2 msA (LA_TEXTS + 8 * ((d / 8) mod 11)) tp) in *.
          assert (HEI2 : img_env pa_val A_LIM E2) by (unfold E2, at_E2; apply Eimg_env).
          assert (E233 : ew E2 33%nat = w64 tp)
            by (unfold E2, at_E2; rewrite Eimg_low by (unfold A_TEXT; lia);
                exact (ew_Ereg_extra _ [w64 (LA_TEXTS + 8 * ((d / 8) mod 11)); w64 tp] 1)).
          pose proof HS2 as HS20.
          paj_run_to_tok RUNTO HS2 HJ SHOK2 hd_span (kpc KP_TXT).
          { exact (at_awr2 E2). }
          lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?mm) => rename mm into msF end.
          repeat rewrite wvb_collapse in HJ.
          prreg HS2 (Z_to_bv 5 27) R27.
          pose proof (kh_reg_same E2 _ _ (w_H W3) msA msF at_keepz2 HS20 HS2 ltac:(vm_compute; reflexivity)) as KR2.
          lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
            pose proof (kept_of_frame (segs := SEGS) E2 _ (w_H W3) (ms_mem msA) (ms_mem msF)
              (fun _ => False) HFr (at_win2 E2)) as UN2;
            pose proof (fun a Hp => kh_apres_grows _ _ _ a HG Hp) as HP2 end.
          lazymatch goal with HJ' : ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdF _ |- SRr _ _ (mkCfg _ ?mdF) _ =>
            assert (Hmd : m_fds mdF = m_fds md3 /\ m_fs mdF = m_fs md3)
              by (split; [repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
                         | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity]) end.
          assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
                     aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
          { intros a Ha Hn. rewrite (UN2 a Ha (fun x => x)). exact (UN1 a Ha Hn). }
          assert (VP : au64_at SEGS (rdW W3 (ms_mem msF)) (ka0 cx) (k_wp cx + (adv + 1))).
          { apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem msA) (ms_mem msF) (ka0 cx) (ka0 cx) 8 _); [|exact VPA].
            intros i Hi. cbn in Hi. apply UN2; [lia | intros []]. }
          assert (VN : au64_at SEGS (rdW W3 (ms_mem msF)) (ka0 cx + 8) (k_wn cx - (adv + 1))).
          { apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem msA) (ms_mem msF) (ka0 cx + 8) (ka0 cx + 8) 8 _);
              [|exact VNA].
            intros i Hi. cbn in Hi. apply UN2; [lia | intros []]. }
          destruct (at_land msF _ KP_TXT (adv + 1) [(23%nat, d); (27%nat, tp)]
            (at_kms E2 _ msF KP_TXT HS2 eq_refl ltac:(vm_compute; reflexivity))
            (fun r Hr => eq_trans (KR2 r (at_keep_sub _ Hr)) (KR1 r Hr))
            ltac:(unfold kregs_eq; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
                  try change (Z.of_nat 23) with 23; try change (Z.of_nat 27) with 27;
                  [rewrite (KR2 (Z_to_bv 5 23) ltac:(vm_compute; reflexivity)); exact R23'
                  | rewrite R27; first [exact E233 | apply sv_off0; exact E233]])
            UN (fun a Hp => HP2 a (HP1 a Hp)) (proj1 Hmd) (proj2 Hmd) ltac:(lia) VP VN)
            as (HKF & HWF).
          exact (CTXT d tp msF _ Hbr HTP HKS HJ HKF HWF).
      -
          remember (at_E1 ms3 (k_wp cx + adv) (k_wn cx - adv) d s) as E eqn:HEdef.
          assert (HS : st_ok_pi SEGS pa_val E (at_ss1 false) (restrict (w_H W3) ms3))
            by (rewrite HEdef; exact (at_seat1 false s b Hadv Hs Hsok Hb Hf)).
          assert (EF : ew E 18%nat = w64 (ka0 cx) /\ ew E 32%nat = w64 (k_wp cx + adv) /\
                       ew E 33%nat = w64 (k_wn cx - adv) /\ ew E 34%nat = w64 d).
          { rewrite HEdef. destruct (at_Ef (k_wp cx + adv) (k_wn cx - adv) d s)
              as (E18 & _ & _ & E32 & E33 & E34 & _). tauto. }
          destruct EF as (E18 & E32 & E33 & E34).
          assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; unfold at_E1; apply Eimg_env).
          assert (BV18u : bv_unsigned (ew E 18%nat) = ka0 cx) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
          assert (BV18 : base_val E (Some 18%nat) = ka0 cx) by (cbn [base_val]; exact BV18u).
          assert (SHOK : sh_ok SEGS hd_Bx hd_SH E (mrestrict (w_H W3) (ms_mem ms3))) by (rewrite HEdef; apply at_shok).
          assert (DP : sv_denot E (SOff 32 1) = Z_to_bv 64 (k_wp cx + (adv + 1))).
          { cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
          assert (DN : sv_denot E (SOff 33 (-1)) = Z_to_bv 64 (k_wn cx - (adv + 1))).
          { cbn [sv_denot]. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
          pose proof HS as HS0. pose proof HJ3 as HJ.
          (* stage 1 *)
          paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc 0xa30).
          { exact (at_awr1 E BV18). }
          lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mm) => rename mm into msA end.
          repeat rewrite wvb_collapse in HJ.
          spregion HS 0%nat HR0.
          prreg HS (Z_to_bv 5 23) R23A.
          pose proof (kh_reg_same E _ _ (w_H W3) ms3 msA hd_keepz HS0 HS ltac:(vm_compute; reflexivity)) as KR1.
          lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
            pose proof (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem msA)
              (fun a => ka0 cx <= a < ka0 cx + 16) HFr (at_win1 E BV18)) as UN1;
            pose proof (fun a Hp => kh_apres_grows _ _ _ a HG Hp) as HP1; clear HFr HG end.
          pose proof (at_curw E msA _ _ _ _ _ 0 (SOff 32 1) _ HR0 BV18u ltac:(at_inl) DP ltac:(lia)) as VPA.
          rewrite Z.add_0_r in VPA.
          pose proof (at_curw E msA _ _ _ _ _ 8 (SOff 33 (-1)) _ HR0 BV18u ltac:(at_inl) DN ltac:(lia)) as VNA.
          pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ msA HS eq_refl) as ShA.
          lazymatch type of ShA with msA = mkst _ (Z_to_bv 64 (_ + ss_pc ?ssx)) _ _ =>
            assert (PcA : ss_pc ssx = kpc 0xa30) by (vm_compute; reflexivity) end.
          rewrite PcA in ShA.
          assert (R23' : getr (ms_regs msA) (Z_to_bv 5 23) = w64 d) by (rewrite R23A; first [exact E34 | apply sv_off0; exact E34]).
          assert (R20' : getr (ms_regs msA) (Z_to_bv 5 20) = w64 SHADOW_OFF).
          { rewrite (KR1 (Z_to_bv 5 20) ltac:(vm_compute; reflexivity)).
            pose proof HK as (_ & (_ & _ & _ & _ & _ & _ & R20) & _). exact R20. }
          clear HS0.
          (* stage 2 *)
          destruct (at_seat2 msA d tp ltac:(rewrite ShA; reflexivity) ltac:(rewrite ShA; reflexivity)
            ltac:(rewrite ShA; reflexivity) ltac:(rewrite ShA; reflexivity) ltac:(rewrite ShA; reflexivity)
            ltac:(rewrite ShA; reflexivity) R23' Hbr R20' UN1 HTP Htp) as (HS2 & SHOK2).
          set (E2 := at_E2 msA (LA_TEXTS + 8 * ((d / 8) mod 11)) tp) in *.
          assert (HEI2 : img_env pa_val A_LIM E2) by (unfold E2, at_E2; apply Eimg_env).
          assert (E233 : ew E2 33%nat = w64 tp)
            by (unfold E2, at_E2; rewrite Eimg_low by (unfold A_TEXT; lia);
                exact (ew_Ereg_extra _ [w64 (LA_TEXTS + 8 * ((d / 8) mod 11)); w64 tp] 1)).
          pose proof HS2 as HS20.
          paj_run_to_tok RUNTO HS2 HJ SHOK2 hd_span (kpc KP_TXT).
          { exact (at_awr2 E2). }
          lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?mm) => rename mm into msF end.
          repeat rewrite wvb_collapse in HJ.
          prreg HS2 (Z_to_bv 5 27) R27.
          pose proof (kh_reg_same E2 _ _ (w_H W3) msA msF at_keepz2 HS20 HS2 ltac:(vm_compute; reflexivity)) as KR2.
          lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
            pose proof (kept_of_frame (segs := SEGS) E2 _ (w_H W3) (ms_mem msA) (ms_mem msF)
              (fun _ => False) HFr (at_win2 E2)) as UN2;
            pose proof (fun a Hp => kh_apres_grows _ _ _ a HG Hp) as HP2 end.
          lazymatch goal with HJ' : ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdF _ |- SRr _ _ (mkCfg _ ?mdF) _ =>
            assert (Hmd : m_fds mdF = m_fds md3 /\ m_fs mdF = m_fs md3)
              by (split; [repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
                         | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity]) end.
          assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
                     aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
          { intros a Ha Hn. rewrite (UN2 a Ha (fun x => x)). exact (UN1 a Ha Hn). }
          assert (VP : au64_at SEGS (rdW W3 (ms_mem msF)) (ka0 cx) (k_wp cx + (adv + 1))).
          { apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem msA) (ms_mem msF) (ka0 cx) (ka0 cx) 8 _); [|exact VPA].
            intros i Hi. cbn in Hi. apply UN2; [lia | intros []]. }
          assert (VN : au64_at SEGS (rdW W3 (ms_mem msF)) (ka0 cx + 8) (k_wn cx - (adv + 1))).
          { apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem msA) (ms_mem msF) (ka0 cx + 8) (ka0 cx + 8) 8 _);
              [|exact VNA].
            intros i Hi. cbn in Hi. apply UN2; [lia | intros []]. }
          destruct (at_land msF _ KP_TXT (adv + 1) [(23%nat, d); (27%nat, tp)]
            (at_kms E2 _ msF KP_TXT HS2 eq_refl ltac:(vm_compute; reflexivity))
            (fun r Hr => eq_trans (KR2 r (at_keep_sub _ Hr)) (KR1 r Hr))
            ltac:(unfold kregs_eq; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
                  try change (Z.of_nat 23) with 23; try change (Z.of_nat 27) with 27;
                  [rewrite (KR2 (Z_to_bv 5 23) ltac:(vm_compute; reflexivity)); exact R23'
                  | rewrite R27; first [exact E233 | apply sv_off0; exact E233]])
            UN (fun a Hp => HP2 a (HP1 a Hp)) (proj1 Hmd) (proj2 Hmd) ltac:(lia) VP VN)
            as (HKF & HWF).
          exact (CTXT d tp msF _ Hbr HTP HKS HJ HKF HWF). }
    destruct (Z.eq_dec s 0) as [Hs0 | Hs0].
    + exact (GO true Hs0).
    + exact (GO false Hs0).
Qed.

End h.

Theorem kn_atxt : forall POST Rc Rm Ra,
  kfrom SK B POST (kin_txt B Rc Rm Ra) -> kfrom SK B POST (kin_acase B Rc Rm Ra KP_A0 ka_empty) ->
  kfrom SK B POST (kin_attr B Rc Rm Ra).
Proof.
  intros POST Rc Rm Ra HTXT HA0 cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & m & k & n & f & adv & hd & kd & left & HRc & HRm & HRa & Hc & Hci & Hj & Hm & Hk &
    Hkd & Hleft & Hhd & HW & _ & HK).
  apply (at_go cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd left HB HJ HK HW (POST cx)).
  - intros ms' md' HJ' HK' HW'. apply (HA0 cx fpos k2 ly3 S3 W3 ms' md' HB HJ' Hfrm).
    exists 0, LA_STR_EMPTY. split; [lia|].
    destruct (at_pre cx HB)
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSE).
    split; [exact HSE|]. split; [split; reflexivity|].
    exists c, ci, j, m, k, n, f, adv, hd, kd, left.
    repeat (split; [eassumption|]). split; [exact I | exact HK'].
  - intros a p ms' md' Ha Hp Hkt HJ' HK' HW'. apply (HTXT cx fpos k2 ly3 S3 W3 ms' md' HB HJ' Hfrm).
    exists a, p. split; [exact Ha|]. split; [exact Hp|]. split; [exact Hkt|].
    exists c, ci, j, m, k, n, f, (adv + 1), hd, kd, left.
    repeat (split; [eassumption|]). split; [exact I | exact HK'].
Qed.

End b.
End a.

Print Assumptions kn_atxt.
