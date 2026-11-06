(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its module names changed; 847 of its 927 lines of code are new or changed and 406 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the message of kind 2
   (lib/A/Prog/kernel_defs.v kin_kind at kd = 2, +0x1178) to the cut after a message (kin_next, +0x1b84). Listing
   (internal path) (internal record, sha256 7bc02d6772b3), +0x1178 .. +0x11bc and +0x1b2c .. +0x1b7c.

   THE CODE. `beqz a3` (+0x1178) on the bytes left (a3 = n - adv, which kin_kind gives for kd <> 0):
   (A) none left: +0x1b2c sets c := 0; nothing is written;
   (B) one or more: the cursor is advanced by one byte (+0x118c stores n - adv - 1, +0x11a4 stores p + adv + 1,
       each behind its instrumented check, which the cursor's shadow entry decides) and the input byte c is read
       at p + adv (+0x11b8, behind the check of its shadow, which the input byte's shadow entry decides).
   Both arms reach +0x1b30 with c in a2. Then +0x1b30 .. +0x1b74: a1 := msg_build.codes[c & 3] (`lw` +0x1b58,
   sign-extended; its value only goes to nl_error's a1, which nl_error's Pre leaves free) and
   a2 := (slti(sext8 c < 0) - 1) | ((c & 0xff) >> 4 & 7). +0x1b7c calls nl_error; kernel_k12_call.v `kn_ncall`
   does the call and the step to kin_next.

   WHY THE WALK IS SPLIT AT +0x1b30. One symbolic state carrying BOTH the input byte's region (base = the cursor
   pointer) and msg_build.codes' region needs `pairwise_disjoint`, i.e. the input apart from the codes table, and
   NO premise of kernel_c.v gives that (`kernel_apart` separates each of them from the frame, g_nl, long_alias and
   the cursor only). So stage 1 carries the cursor and input regions and stops at +0x1b30 (k2_armA, k2_armB), and
   stage 2 (k2_stage2) starts there from a FRESH `sr_atoms` state (a2 = atom 12 = the byte) carrying only the
   codes region. Stage 2 is shared by both arms.

   THE CODES REGION. The `lw` needs a chunk to read: the region has the table's four words as chunks
   `CVal 4 (SOff 32..35 0)`, the four values being the extras of stage 2's env. They are read off the call's bytes
   (kernel_apre: `abytes .. LA_MSG_CODES cs`), moved to the cut by k2_codes_at (kernel_kit.v kn_input_at's second
   half at the codes: akept_akb_gx, the codes being apart from kernel's writes and from F's side bytes) and on to
   stage 2's state, which differs from the cut only in the cursor (the codes are apart from it, kernel_apart).

   THE TABLE INDEX AND THE CUT WORD. c & 3 is symbolic, so the engine stops at the `lw`: stage 2 runs to +0x1b34
   and the proof cases on c mod 4 = 0..3, pins a0 to that LITERAL (LinkPaLib st_ok_pi_pin_reg') and runs on to the
   call in each case (a run on a state holding a Coq variable does not terminate). The index (k2_eidx_val) and
   the cut word a2 (k2_ecut_ok) are read off the engine's own expressions by a case split over the 256 byte
   values, as kernel_msg0_c.v mc_m6_val does: each case is a closed `vm_compute`, so the kernel re-checks 256
   small closed evaluations. (Doing it instead through one `forallb .. (seq 0 256) = true` table consumed by a
   `forall g` helper costs 631 s at Qed: the kernel then has to convert two differently shaped `forallb` terms and
   evaluates `seq 0 256` with no VM. Measured on this file, 2026-10-30.) a2 is 2 ^ 64 - 1 when c < 128 and 0..7
   otherwise, so it meets nl_error's premise `a2 <= NL_ERR_BODY \/ 2 ^ 63 <= a2` either way.

   THE CUT RE-ESTABLISHED. The runs write only the cursor's 16 bytes, so kernel_kit.v kat_reframe moves every
   clause of the cut and the new cursor words are the end state's region chunks (k2_land), at adv + 1 on arm (B)
   and at adv on arm (A).

   Callees: nl_error, through kernel_k12_call.v (ANLERR). Section hypotheses used: LAWS, LV, KI, TB, ANLERR.
   Released proofs (rule 24): none of kernel's walk (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by
   the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_error_c kernel_c kernel_img kernel_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalkCall PcapRelro kernel_kit kernel_entry kernel_next kernel_ocall kernel_k12_call kernel_msg0_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the join of the two arms: +0x1b30, `andi a0, a2, 3` with the byte in a2 *)
Definition KP_CODE : Z := 0x1b30.

Definition k2_Bx : sv := SOff 20 0.
Definition k2_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow cell of atom r + o (kernel_msg0_kit.v km_sh, whose denotation lemma this file uses) *)
Definition k2_sh (r : nat) (o : Z) : sv := km_sh r o.

(* ---- stage 1, arm (B): the cursor, the slot shadow(a0) and the input byte ---- *)
Definition k2_regs : list sv := sr_set sr_atoms (Z_to_bv 5 (Z.of_nat 24)) (k2_sh 18 8).
Definition k2_rgS : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0 0 [YP09.mkChunk 0xc0 (CVal 8 (k2_sh 18 0))].
Definition k2_rgCur : YP09.region := YP09.mkRegion (Some 18%nat) 0 16 0 16 [].
Definition k2_rgIn : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition k2_SHB : list shent := [mkSHE 18 0 16; mkSHE 10 0 1].
Definition k2_fB : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (18%nat, mkAF 4096 (2 ^ 47 - 16) 0); (10%nat, mkAF 4096 (2 ^ 47 - 1) 0);
           (13%nat, mkAF 1 (2 ^ 64 - 1) 0); (32%nat, mkAF 0 255 0)] [] [].
Definition k2_ssB : sstate := mkSS (kpc KP_K2) k2_regs [k2_rgS; k2_rgCur; k2_rgIn] None k2_fB.

(* ---- stage 1, arm (A): a3 pinned to 0, no region ---- *)
Definition k2_fA : facts := mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition k2_ssA : sstate :=
  mkSS (kpc KP_K2) (sr_set sr_atoms (Z_to_bv 5 (Z.of_nat 13)) (SLit 0)) [] None k2_fA.

(* ---- stage 2 (shared): a fresh state at +0x1b30 with only msg_build.codes, its four words the extras 32..35 ---- *)
Definition k2_rgCo : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 22)) 0 16 0 0
    [YP09.mkChunk 0 (CVal 4 (SOff 32 0)); YP09.mkChunk 4 (CVal 4 (SOff 33 0));
     YP09.mkChunk 8 (CVal 4 (SOff 34 0)); YP09.mkChunk 12 (CVal 4 (SOff 35 0))].
Definition k2_SHC : list shent := [mkSHE (A_OBJ 22) 0 16].
Definition k2_fC : facts :=
  mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (12%nat, mkAF 0 255 0);
           (A_OBJ 22, mkAF 0x210e0 0x210e0 0)] [] [].
Definition k2_ssC : sstate := mkSS (kpc KP_CODE) sr_atoms [k2_rgCo] None k2_fC.

(* ---- the engine's own expressions for the code index and the cut word, over the byte in a2 ---- *)
Definition k2_eidx : sv := SAlu ALU_AND (SOff 12 0) (SLit 3).
Definition k2_ecut : sv :=
  SAlu ALU_OR
    (SAlu ALU_ADD
       (SAlu ALU_SLT (SAlu ALU_SRA (SAlu ALU_SLL (SOff 12 0) (SLit 56)) (SLit 56)) (SLit 0))
       (SLit (-1)))
    (SAlu ALU_AND (SAlu ALU_SRL (SAlu ALU_AND (SOff 12 0) (SLit 255)) (SLit 4)) (SLit 7)).

(* the byte's 256 values, as kernel_msg0_c.v mc_m6_val lists them *)
Lemma k2_bytes : forall c, 0 <= c < 256 -> In c (map Z.of_nat (seq 0 256)).
Proof.
  intros c Hc. apply in_map_iff. exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Lemma k2_eidx_val : forall (E : env) c, ew E 12%nat = Z_to_bv 64 c -> 0 <= c < 256 ->
  sv_denot E k2_eidx = Z_to_bv 64 (c mod 4).
Proof.
  intros E c Hc Hr. unfold k2_eidx. cbn [sv_denot]. rewrite !Hc.
  pose proof (k2_bytes c Hr) as Hin. clear Hr. cbn [seq map] in Hin.
  repeat (destruct Hin as [<- | Hin]; [apply bv_eq; vm_compute; reflexivity |]). destruct Hin.
Qed.

Lemma k2_ecut_ok : forall (E : env) c, ew E 12%nat = Z_to_bv 64 c -> 0 <= c < 256 ->
  bv_unsigned (sv_denot E k2_ecut) <= NL_ERR_BODY \/ 2 ^ 63 <= bv_unsigned (sv_denot E k2_ecut).
Proof.
  intros E c Hc Hr. unfold k2_ecut. cbn [sv_denot]. rewrite !Hc.
  pose proof (k2_bytes c Hr) as Hin. clear Hr. cbn [seq map] in Hin.
  repeat (destruct Hin as [<- | Hin];
          [first [left; vm_compute; discriminate | right; vm_compute; discriminate] |]).
  destruct Hin.
Qed.

(* a byte of memory as a one-byte value (kernel_msg0_c.v's proof of its input chunk) *)
Lemma k2_val1 : forall segs (m : word -> option byte) a (b : byte),
  mbyte segs m a = Some b -> val_mem segs m a 1 (bv_unsigned b).
Proof.
  intros segs m a b Hb kk Hk. destruct kk as [|kk]; [|cbn in Hk; lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb.
  pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  rewrite le_byte_small by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia).
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* an atom's value under an environment a run extended above 32 *)
Lemma k2_ew_set : forall (E : env) (nn mm : nat) w, nn <> mm -> ew (ewset E nn w) mm = ew E mm.
Proof.
  intros E nn mm w H. cbn [ew ewset].
  (rewrite (proj2 (Nat.eqb_neq nn mm) H)
   || rewrite (proj2 (Nat.eqb_neq mm nn) (fun e => H (eq_sym e)))).
  reflexivity.
Qed.

(* the registers and extras agree with an environment a run extended at an atom K >= 32 *)
Lemma k2_agree_set : forall E0 (E : env) (K : nat) w, env_agree 32 E0 E -> (32 <= K)%nat ->
  env_agree 32 E0 (ewset E K w).
Proof.
  intros E0 E K w [H1 H2] HK. split.
  - intros q Hq. rewrite k2_ew_set by lia. exact (H1 q Hq).
  - exact H2.
Qed.

(* a register the symbolic file names by a value the machine already has (kernel_msg0_c.v mc_regs_ok_set) *)
Lemma k2_regs_ok_set : forall E sr regs (rd : bv 5) e,
  regs_ok E sr regs -> bv_eqb rd 0 = false -> sv_denot E e = getr regs rd ->
  regs_ok E (sr_set sr rd e) regs.
Proof.
  intros E sr regs rd e H H0 He r. destruct (bv_eqb r rd) eqn:Heq.
  - unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq. subst r. rewrite sr_get_set_same by exact H0.
    rewrite He. reflexivity.
  - rewrite sr_get_set_other by (intros ->; rewrite bv_eqb_refl in Heq; discriminate). apply H.
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
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis ANLERR : nl_error_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

(* U of an atom at offset 0 *)
Lemma k2_U0 : forall (E : env) (mt : nat) p, bv_unsigned (ew E mt) = p -> 0 <= p < 2 ^ 64 ->
  U E (SOff mt 0) = p.
Proof.
  intros E mt p Hp Hr. rewrite U_SOff, Hp, Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.

(* the code table is addressable at a cut *)
Lemma k2_codes_ra : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF LA_MSG_CODES 16.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hjb Hkk.
  pose proof HB as (_ & _ & HKP & _).
  destruct HKP as (kbs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hra & _).
  apply ra_of_saddr. intros x Hx.
  apply (kn_rd_saddr SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 x HB HJ Hjb Hkk).
  - unfold kernel_ard. right; right; right; right; left. exact Hx.
  - exact (saddr_of_ra (aview SEGS (w_H (k_W cx)) (k_memc cx)) LA_MSG_CODES 16 x Hra Hx).
Qed.

(* msg_build.codes at a cut: the call's bytes (kernel_kit.v kn_input_at's second half, at the codes) *)
Lemma k2_codes_at : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 x,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  LA_MSG_CODES <= x < LA_MSG_CODES + 16 ->
  aview SEGS (w_H W3) (ms_mem ms3) x = aview SEGS (w_H (k_W cx)) (k_memc cx) x.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 x HB Hjb Hkk Hx.
  pose proof HB as (HPRE & HRD & HKP & _).
  pose proof HPRE as (HJ0 & _).
  destruct HKP as (kbs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hap & _).
  assert (Hxa : kernel_ard SEGS (k_regs cx) (km0 cx) x)
    by (unfold kernel_ard; right; right; right; right; left; exact Hx).
  pose proof Hjb as (_ & _ & _ & Hnin & (S1 & W1 & mem1 & md1 & HAR1 & HF1 & _) & _).
  assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite HF1; left; reflexivity).
  pose proof HAR1 as (M1 & _).
  destruct (frame_facts B _ _ _ KN_CID fpos M1 Hin1) as (_ & Hpos & _).
  destruct Hkk as (Hak & _).
  eapply (akept_akb_gx SK SEGS B); [exact HJ0 | exact Hak | exact (HRD x Hxa) |].
  intros [HE | HS].
  - unfold kE, inFP in HE. destruct HE as (r & Hin & Hr). unfold kernel_awr in Hin. cbn [In] in Hin.
    destruct Hap as (_ & Hg & Hl & Hc).
    unfold apart_gnl, apart in *. unfold NK_CHUNK, NK_OPEN, NK_SIZE, LONG_ALIAS_SIZE in *.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
  - exact (akb_not_side SK SEGS B pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos x HJ0
      ltac:(unfold KN_CID; lia) Hpos Hnin (HRD x Hxa) HS).
Qed.

(* a word of the codes, as the 4-byte value a chunk names *)
Lemma k2_codes_vals : forall (m : word -> option byte) cs off,
  abytes SEGS m LA_MSG_CODES cs -> length cs = 16%nat -> 0 <= off -> off + 4 <= 16 ->
  exists v, 0 <= v < 2 ^ 32 /\ val_mem SEGS m (LA_MSG_CODES + off) 4 v.
Proof.
  intros m cs off Hab Hl H0 H4.
  pose proof (val_mem_u32 SEGS m LA_MSG_CODES cs off Hab H0 ltac:(rewrite Hl; lia)) as Hv.
  exists (rdn cs off 4). split; [|exact Hv].
  unfold rdn.
  pose proof (bytes_le_to_Z_nonneg (slice cs off 4)) as Hn.
  pose proof (bytes_le_to_Z_bound (slice cs off 4)) as Hb.
  rewrite lw_slice_length in Hb by (rewrite ?Hl; lia).
  change (2 ^ (8 * Z.of_nat (Z.to_nat 4))) with (2 ^ 32) in Hb. lia.
Qed.

(* the cursor's bytes may be written: the call's ajw, moved to the cut's journal (kernel_msg0_c.v mc_awr_cur) *)
Lemma k2_awr_cur : forall cx fpos k2 ly3 S3 W3 mm md3, kbase SK B cx ->
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

(* ---- THE LANDING: the runs wrote only the cursor's 16 bytes ---- *)
Lemma k2_land : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 (msn : machine_state) mdn
    pc pc' rl rl' sl adv adv' g,
  kbase SK B cx ->
  kjbk B cx fpos k2 ly3 S3 md3 ->
  kat B cx fpos pc rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' msn -> kregs0 cx msn -> kregs_eq msn rl' ->
  m_fds mdn = m_fds md3 -> m_fs mdn = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem msn) a) ->
  kslots_okb sl = true ->
  0 <= adv' <= k_wn cx ->
  au64_at SEGS (rdW W3 (ms_mem msn)) (ka0 cx) (k_wp cx + adv') ->
  au64_at SEGS (rdW W3 (ms_mem msn)) (ka0 cx + 8) (k_wn cx - adv') ->
  kat B cx fpos pc' rl' sl (kfsh 0xf8 0 0xf3) true adv' g k2 ly3 S3 W3 msn mdn.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 msn mdn pc pc' rl rl' sl adv adv' g
    HB HJB HK HMS HR0 HRL Hfds Hfs UN HP Hsl Hadv' Hp' Hn'.
  pose proof HK as (_ & _ & _ & _ & _ & HSH & HSL & _ & _ & HCUR & _).
  pose proof (kn_apre SK B cx HB) as (Agnl & Ala & _).
  pose proof (kn_sp SK B cx HB) as (Hac & Hsp2 & _ & Hs1 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity.
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  rewrite Hfb in F2.
  assert (HFS : kFSH cx fpos = SHADOW_OFF + kF cx fpos / 8) by reflexivity.
  assert (CARD : forall a, ka0 cx <= a < ka0 cx + 16 -> kernel_ard SEGS (k_regs cx) (km0 cx) a)
    by (intros a Ha; exact (kn_ard_cur cx a Ha)).
  assert (Msv : forall a, ksp cx - 104 <= a < ksp cx -> ~ (ka0 cx <= a < ka0 cx + 16)).
  { intros a Ha Hc. destruct (kn_ard_bound SK B LAWS cx a HB (CARD a Hc)) as (_ & Hn). apply Hn. lia. }
  assert (Mhd : forall a, kF cx fpos <= a < kF cx fpos + 24 -> ~ (ka0 cx <= a < ka0 cx + 16)).
  { intros a Ha Hc. apply (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB (CARD a Hc)).
    rewrite Hfb. lia. }
  assert (Mfl : forall a, kF cx fpos + fs_frame_bytes KN_CID - 8 <= a < kF cx fpos + fs_frame_bytes KN_CID ->
            ~ (ka0 cx <= a < ka0 cx + 16)).
  { intros a Ha Hc. apply (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB (CARD a Hc)).
    rewrite Hfb in Ha |- *. lia. }
  assert (Msh : forall a, kFSH cx fpos <= a < kFSH cx fpos + Z.of_nat (length (kfsh 0xf8 0 0xf3)) ->
            ~ (ka0 cx <= a < ka0 cx + 16)).
  { rewrite kfsh_length. intros a Ha Hc.
    destruct (kn_rd_facts SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB (CARD a Hc)) as (_ & Hband & _).
    apply Hband. rewrite HFS in Ha. unfold SHADOW_OFF in *. lia. }
  assert (Mgn : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ (ka0 cx <= a < ka0 cx + 16)).
  { intros a Ha Hc. unfold apart_gnl in Agnl. lia. }
  assert (Mla : forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + LONG_ALIAS_SIZE ->
            ~ (ka0 cx <= a < ka0 cx + 16)).
  { intros a Ha Hc. unfold apart, LONG_ALIAS_SIZE in Ala. unfold LONG_ALIAS_SIZE in Ha. lia. }
  apply (kat_reframe SK B LAWS (fun a => ka0 cx <= a < ka0 cx + 16) cx fpos pc rl sl (kfsh 0xf8 0 0xf3) true
           adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl (kfsh 0xf8 0 0xf3) adv' W3 msn mdn
           HB HK HMS HR0 HRL Hfds Hfs UN HP).
  - intros a Ha. left. unfold kE, inFP.
    exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
    split; [cbn [In kernel_awr]; right; right; left; reflexivity|].
    cbn [fst snd]. unfold ka0 in Ha. exact Ha.
  - exact Msv.
  - exact Mhd.
  - exact Mfl.
  - exact Mgn.
  - exact Mla.
  - exact (kshadow_frame B LAWS (fun a => ka0 cx <= a < ka0 cx + 16) cx fpos (kfsh 0xf8 0 0xf3) k2 ly3 S3 md3
             W3 ms3 W3 msn HJB UN (kfsh_fits 0xf8 0 0xf3) Msh HSH).
  - refine (kslots_frame SK B (fun a => ka0 cx <= a < ka0 cx + 16) cx sl sl W3 ms3 W3 msn HB UN
             (incl_refl _) _ HSL).
    intros ov Hov. pose proof (kslots_okb_spec sl Hsl ov Hov) as Hb.
    split; [exact Hb|]. intros a Ha Hc.
    destruct (kn_ard_bound SK B LAWS cx a HB (CARD a Hc)) as (_ & Hn). apply Hn. lia.
  - destruct HCUR as (_ & _ & _ & HCW).
    split; [exact Hadv'|]. split; [exact Hp'|]. split; [exact Hn'|].
    intros i Hi.
    exact (writable_at_grows SEGS _ _ _ (kk_grows_of_apresent (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem msn) HP)
             (HCW i Hi)).
Qed.

(* the cut's registers and slots at the kind's entry, and at nl_error's entry *)
Definition k2_rl (cx : kcx) (fpos m : Z) : list (nat * Z) :=
  [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
   (22%nat, m); (16%nat, 2)].
Definition k2_sl (cx : kcx) (fpos c ci m k : Z) : list (Z * Z) :=
  kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)].
Definition k2_rlc (cx : kcx) (fpos m cut : Z) : list (nat * Z) :=
  [(1%nat, BASE + kpc KP_NLRET); (10%nat, kW2 cx fpos); (12%nat, cut);
   (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, m)].

(* ---- THE END: the cut at nl_error's entry, from a run that stopped at the call ---- *)
Lemma k2_fin : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    (msn : machine_state) mdn c ci j m k n f adv adv' cut,
  kfrom SK B POST (kin_ncall B Rc Rm) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem msn) mdn k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K2 (k2_rl cx fpos m) (k2_sl cx fpos c ci m k) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  kms KP_NLERR msn -> kregs0 cx msn ->
  getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 1)) = w64 (BASE + kpc KP_NLRET) ->
  getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 10)) = w64 (kW2 cx fpos) ->
  getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 12)) = w64 cut ->
  (forall r, In r nx_keepN ->
     getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))) ->
  m_fds mdn = m_fds md3 -> m_fs mdn = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem msn) a) ->
  0 <= adv' <= k_wn cx ->
  au64_at SEGS (rdW W3 (ms_mem msn)) (ka0 cx) (k_wp cx + adv') ->
  au64_at SEGS (rdW W3 (ms_mem msn)) (ka0 cx + 8) (k_wn cx - adv') ->
  0 <= cut < 2 ^ 64 -> (cut <= NL_ERR_BODY \/ 2 ^ 63 <= cut) ->
  SRr SEGS W3 (mkCfg msn mdn) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 msn mdn c ci j m k n f adv adv' cut
    HC HB HJn HFR HRc HRm Hc Hci Hj Hm Hk HW HAT HMSn HR0n Q1 Q10 Q12 HKN Hfds Hfs UN HP Hadv' Hp' Hn'
    Hcut0 Hcutb.
  pose proof HAT as (_ & _ & HRL & _ & _ & _ & _ & HJB & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity. rewrite Hfb in F2.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HWK : kw_at W3 msn (kW2 cx fpos) n f).
  { apply (kn_kw_keep W3 ms3 msn (kW2 cx fpos) n f HW); [|exact HP].
    intros i Hi. apply UN; [unfold kW2, KN_W2, NW_SIZE in *; lia|].
    intros Hcur.
    apply (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 (kW2 cx fpos + i) HB HJB
             (kn_ard_cur cx (kW2 cx fpos + i) Hcur)).
    rewrite Hfb. unfold kW2, KN_W2, NW_SIZE in *. lia. }
  apply (HC cx fpos k2 ly3 S3 W3 msn mdn HB HJn HFR).
  exists c, ci, j, m, k, n, f, adv', cut.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hm|]. split; [exact Hk|]. split; [exact Hcut0|]. split; [exact Hcutb|].
  split; [exact HWK|].
  refine (k2_land cx fpos k2 ly3 S3 W3 ms3 md3 msn mdn KP_K2 KP_NLERR (k2_rl cx fpos m)
           (k2_rlc cx fpos m cut) (k2_sl cx fpos c ci m k) adv adv' (Some j)
           HB HJB HAT HMSn HR0n _ Hfds Hfs UN HP ltac:(reflexivity) Hadv' Hp' Hn').
  unfold kregs_eq, k2_rl in HRL. rewrite !Forall_cons_iff in HRL.
  destruct HRL as (_ & P21 & P24 & P25 & P22 & _). cbn [fst snd] in P21, P24, P25, P22.
  unfold kregs_eq, k2_rlc. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - exact Q1.
  - exact Q10.
  - exact Q12.
  - rewrite HKN by (unfold nx_keepN; kn_in). exact P21.
  - rewrite HKN by (unfold nx_keepN; kn_in). exact P24.
  - rewrite HKN by (unfold nx_keepN; kn_in). exact P25.
  - rewrite HKN by (unfold nx_keepN; kn_in). exact P22.
Qed.

(* ---- STAGE 2: +0x1b30 -> the call, shared by both arms ---- *)
Lemma k2_stage2 : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    (ms1 : machine_state) md1 c ci j m k n f adv adv' cb,
  kfrom SK B POST (kin_ncall B Rc Rm) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms1) md1 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K2 (k2_rl cx fpos m) (k2_sl cx fpos c ci m k) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  kms KP_CODE ms1 -> kregs0 cx ms1 ->
  (forall r, In r nx_keepN ->
     getr (ms_regs ms1) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))) ->
  getr (ms_regs ms1) (Z_to_bv 5 (Z.of_nat 12)) = w64 cb -> 0 <= cb < 256 ->
  m_fds md1 = m_fds md3 -> m_fs md1 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
     aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms1) a) ->
  0 <= adv' <= k_wn cx ->
  au64_at SEGS (rdW W3 (ms_mem ms1)) (ka0 cx) (k_wp cx + adv') ->
  au64_at SEGS (rdW W3 (ms_mem ms1)) (ka0 cx + 8) (k_wn cx - adv') ->
  SRr SEGS W3 (mkCfg ms1 md1) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 ms1 md1 c ci j m k n f adv adv' cb
    HC HB HJ3 HJ1 HFR HRc HRm Hc Hci Hj Hm Hk HW HAT HMS1 HR01 HKN1 Q12 Hcb Hfds1 Hfs1 UN1 HP1 Hadv' Hp1 Hn1.
  pose proof HAT as (_ & _ & HRL & _ & _ & _ & _ & HJB & HKK & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HMS1 as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof HR01 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity. rewrite Hfb in F2.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  (* the call's codes bytes, at ms1: they are apart from the cursor, the only bytes the arms wrote *)
  pose proof HB as (_ & _ & HKP & _).
  destruct HKP as (kbs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (cs & Hcs & Hcsl) & _ & Hap & _).
  destruct Hap as (_ & _ & _ & HapC). unfold apart in HapC.
  change (aarg (k_regs cx) 0) with (ka0 cx) in HapC.
  assert (HCUT : forall x, LA_MSG_CODES <= x < LA_MSG_CODES + 16 -> ~ (ka0 cx <= x < ka0 cx + 16))
    by (intros x Hx Hc0; unfold LA_MSG_CODES in *; lia).
  assert (HCOB : forall x, LA_MSG_CODES <= x < LA_MSG_CODES + 16 ->
            aview SEGS (w_H W3) (ms_mem ms1) x = aview SEGS (w_H (k_W cx)) (k_memc cx) x).
  { intros x Hx. rewrite (UN1 x ltac:(unfold LA_MSG_CODES in *; lia) (HCUT x Hx)).
    exact (k2_codes_at cx fpos k2 ly3 S3 W3 ms3 md3 x HB HJB HKK Hx). }
  assert (HAB1 : abytes SEGS (rdW W3 (ms_mem ms1)) LA_MSG_CODES cs).
  { destruct Hcs as (Ha & Hal & Hb). split; [exact Ha|]. split; [exact Hal|].
    intros i Hi. rewrite Hcsl in Hi. rewrite <- (Hb i ltac:(rewrite Hcsl; exact Hi)).
    unfold km0. apply mbyte_of_aview. apply HCOB. unfold LA_MSG_CODES. lia. }
  assert (HCORA : range_addressable (aview SEGS (w_H W3) (ms_mem ms1)) SHADOW_OFF LA_MSG_CODES 16).
  { pose proof (k2_codes_ra cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ3 HJB HKK) as HRA3.
    apply ra_of_saddr. intros x Hx. destruct (HRA3 x Hx) as (s & Hs & Hsok).
    exists s. split; [|exact Hsok].
    rewrite (UN1 (shadow_of_addr SHADOW_OFF x)
               ltac:(unfold shadow_of_addr, LA_MSG_CODES, SHADOW_OFF in *; lia)
               ltac:(intros Hc0; destruct (CL (shadow_of_addr SHADOW_OFF x) Hc0) as ([Hq|Hq] & _);
                     unfold shadow_of_addr, kLowMemEnd, kHighMemBeg, LA_MSG_CODES, SHADOW_OFF in *; lia)).
    exact Hs. }
  destruct (k2_codes_vals (rdW W3 (ms_mem ms1)) cs 0 HAB1 Hcsl ltac:(lia) ltac:(lia)) as (v0 & Hv0r & Hv0).
  destruct (k2_codes_vals (rdW W3 (ms_mem ms1)) cs 4 HAB1 Hcsl ltac:(lia) ltac:(lia)) as (v1 & Hv1r & Hv1).
  destruct (k2_codes_vals (rdW W3 (ms_mem ms1)) cs 8 HAB1 Hcsl ltac:(lia) ltac:(lia)) as (v2 & Hv2r & Hv2).
  destruct (k2_codes_vals (rdW W3 (ms_mem ms1)) cs 12 HAB1 Hcsl ltac:(lia) ltac:(lia)) as (v3 & Hv3r & Hv3).
  assert (R21 : getr (ms_regs ms1) (Z_to_bv 5 (Z.of_nat 21)) = w64 (kW2 cx fpos)).
  { rewrite (HKN1 21%nat ltac:(unfold nx_keepN; kn_in)).
    exact (kn_reg_in ms3 _ 21%nat (kW2 cx fpos) HRL ltac:(unfold k2_rl; kn_in)). }
  remember (Eimg (Ereg (ms_regs ms1) [w64 v0; w64 v1; w64 v2; w64 v3])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms1) [w64 v0; w64 v1; w64 v2; w64 v3]) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms1) r)
    by (intros jn r Hjr; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (EXT : forall jn, (jn < 4)%nat ->
            ew E (32 + jn) = nth jn [w64 v0; w64 v1; w64 v2; w64 v3] (Z_to_bv 64 0))
    by (intros jn Hjn; rewrite HEdef, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
  pose proof (EXT 2%nat ltac:(lia)) as E34. pose proof (EXT 3%nat ltac:(lia)) as E35.
  cbn [nth Nat.add] in E32, E33, E34, E35.
  assert (E20 : ew E 20%nat = w64 SHADOW_OFF) by (rewrite (ER 20%nat 20%bv eq_refl); exact R20).
  assert (E12 : ew E 12%nat = w64 cb)
    by (rewrite (ER 12%nat (Z_to_bv 5 (Z.of_nat 12)) eq_refl); exact Q12).
  assert (E21 : ew E 21%nat = w64 (kW2 cx fpos))
    by (rewrite (ER 21%nat (Z_to_bv 5 (Z.of_nat 21)) eq_refl); exact R21).
  assert (B20 : bv_unsigned (ew E 20%nat) = SHADOW_OFF)
    by (rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (B12 : bv_unsigned (ew E 12%nat) = cb) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (B21 : bv_unsigned (ew E 21%nat) = kW2 cx fpos)
    by (rewrite E21; apply unsigned_lit_small; unfold kW2, KN_W2; lia).
  assert (Eco : ew E (A_OBJ 22) = w64 LA_MSG_CODES).
  { rewrite HEdef, Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj LV 22%nat ltac:(unfold link_nobj; lia)). reflexivity. }
  assert (Bco : bv_unsigned (ew E (A_OBJ 22)) = LA_MSG_CODES)
    by (rewrite Eco; apply unsigned_lit_small; unfold LA_MSG_CODES; lia).
  assert (HS : st_ok_pi SEGS pa_val E k2_ssC (restrict (w_H W3) ms1)).
  { rewrite (kn_ms_shape ms1 (BASE + kpc KP_CODE) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold k2_ssC. apply pa_entry_st_ok_full.
    - rewrite HEdef. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold k2_rgCo, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Bco.
      split; [unfold LA_MSG_CODES; lia|]. split; [unfold LA_MSG_CODES; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      + apply (chunk_ok_val SEGS E _ LA_MSG_CODES 0 4 (SOff 32 0) v0);
          [apply sv_off0; exact E32 | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
           | change (Z.of_N 4) with 4; lia | exact Hv0].
      + apply (chunk_ok_val SEGS E _ LA_MSG_CODES 4 4 (SOff 33 0) v1);
          [apply sv_off0; exact E33 | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
           | change (Z.of_N 4) with 4; lia | exact Hv1].
      + apply (chunk_ok_val SEGS E _ LA_MSG_CODES 8 4 (SOff 34 0) v2);
          [apply sv_off0; exact E34 | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
           | change (Z.of_N 4) with 4; lia | exact Hv2].
      + apply (chunk_ok_val SEGS E _ LA_MSG_CODES 12 4 (SOff 35 0) v3);
          [apply sv_off0; exact E35 | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
           | change (Z.of_N 4) with 4; lia | exact Hv3].
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - unfold k2_fC, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; [exact I | exact I]].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B20, B12, Bco.
      change (2 ^ 0) with 1.
      split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
      split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
      split; [|exact I]. split; [unfold LA_MSG_CODES; lia|].
      split; [apply Z.mod_1_r | unfold LA_MSG_CODES; lia]. }
  assert (SHOK : sh_ok SEGS k2_Bx k2_SHC E (mrestrict (w_H W3) (ms_mem ms1))).
  { unfold sh_ok, k2_SHC. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms1) E k2_Bx (A_OBJ 22) LA_MSG_CODES 16 LA_MSG_CODES
             0 16 HCORA ltac:(unfold k2_Bx; apply k2_U0; [exact B20 | unfold SHADOW_OFF; lia]));
      [apply k2_U0; [exact Bco | unfold LA_MSG_CODES; lia] | lia | lia |].
    intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold LA_MSG_CODES, SHADOW_OFF in *. lia. }
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  (* +0x1b30 .. +0x1b34: a0 := c & 3 *)
  paj_run_to_tok RUNTO HS HJ1 SHOK k2_span (kpc 0x1b34).
  { cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. cbn [k2_rgCo YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?mq) |- _ => rename mq into msA end.
  repeat rewrite wvb_collapse in HJ1.
  assert (HmA : ms_mem msA = ms_mem ms1).
  { apply functional_extensionality. intros x.
    lazymatch goal with HFx : frame_of _ _ (ms_mem ms1) (ms_mem msA) |- _ => apply HFx end.
    intros (rr & Hin & Hw). cbn [ss_mem In] in Hin. destruct Hin as [<-|[]].
    cbn [k2_rgCo YP09.r_base YP09.r_wlo YP09.r_whi] in Hw. lia. }
  assert (Hpin : getr (ms_regs msA) (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (cb mod 4)).
  { lazymatch goal with
    | HSx : st_ok_pi _ _ _ ?ssx (restrict _ msA) |- _ =>
      rewrite (st_ok_pi_restrict_reg (w_H W3) E ssx msA (Z_to_bv 5 (Z.of_nat 10)) HSx);
      replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 10))) with k2_eidx by (vm_compute; reflexivity)
    end.
    exact (k2_eidx_val E cb E12 Hcb). }
  assert (CASES : cb mod 4 = 0 \/ cb mod 4 = 1 \/ cb mod 4 = 2 \/ cb mod 4 = 3) by lia.
  destruct CASES as [Hq|[Hq|[Hq|Hq]]]; rewrite Hq in Hpin;
  lazymatch goal with
  | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
    lazymatch type of Hpin with
    | _ = Z_to_bv 64 ?z =>
      pose proof (st_ok_pi_pin_reg' E ssx (restrict (w_H W3) msx) (Z_to_bv 5 (Z.of_nat 10)) z HSx
                    ltac:(cbn [restrict ms_regs]; exact Hpin) ltac:(vm_compute; reflexivity)) as HSP
    end;
    clear HSx
  end;
  lazymatch type of HSP with st_ok_pi _ _ _ ?s _ =>
    let v := eval vm_compute in s in change s with v in HSP end;
  (* +0x1b34 .. the call *)
  (paj_run_tok RUN HSP HJ1 SHOK k2_span;
   [ cbn [ss_mem]; apply awr_ok_x_cons; [|apply awr_ok_x_nil];
     intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia | ]);
  repeat rewrite wvb_collapse in HJ1;
  lazymatch goal with
  | HS2 : st_ok _ ?Ex ?ssy (restrict _ ?msn) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
         assert (HmB : ms_mem msn = ms_mem ms1)
           by (transitivity (ms_mem msA);
               [ apply functional_extensionality; intros x;
                 lazymatch goal with
                 | HFy : frame_of _ _ (ms_mem msA) (ms_mem msn) |- _ =>
                   apply HFy; intros (rr & Hin & Hw); cbn [ss_mem In] in Hin; destruct Hin as [<-|[]];
                   cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia
                 end
               | exact HmA ]);
         assert (EX12 : ew Ex 12%nat = w64 cb)
           by (first [exact E12 | rewrite k2_ew_set by lia; exact E12]);
         assert (EX21 : bv_unsigned (ew Ex 21%nat) = kW2 cx fpos)
           by (first [exact B21 | rewrite k2_ew_set by lia; exact B21]);
         assert (EX240 : ew Ex 240%nat = ew E 240%nat)
           by (first [reflexivity | apply k2_ew_set; lia]);
         assert (EXA : env_agree 32 (Ereg (ms_regs ms1) [w64 v0; w64 v1; w64 v2; w64 v3]) Ex)
           by (split; [intros qa Hqa; rewrite ?k2_ew_set by lia; exact (proj1 HAG qa Hqa)
                      | exact (proj2 HAG)]);
         assert (HMSn : kms KP_NLERR msn)
           by (apply (k12_kms_of _ _ ssy msn KP_NLERR HS2);
               [vm_compute; reflexivity | cbn [ss_pc setpc]; exact k12_sigma_nlerr]);
         assert (HK0 : forall r, In r nx_keep0 -> getr (ms_regs msn) r = getr (ms_regs ms1) r)
           by exact (regs_kept_of_st_ok SEGS Ex ssy (restrict (w_H W3) msn) (ms_regs ms1)
                       [w64 v0; w64 v1; w64 v2; w64 v3] nx_keep0 HS2 EXA ltac:(vm_compute; reflexivity));
         assert (HKN : forall r, In r nx_keepN ->
                   getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms1) (Z_to_bv 5 (Z.of_nat r)))
           by (intros r Hr;
               exact (regs_kept_of_st_ok SEGS Ex ssy (restrict (w_H W3) msn) (ms_regs ms1)
                        [w64 v0; w64 v1; w64 v2; w64 v3]
                        (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) nx_keepN) HS2 EXA
                        ltac:(vm_compute; reflexivity) _ (kn_in_map5 r nx_keepN Hr)));
         assert (Rr1 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 1)) = w64 (BASE + kpc KP_NLRET))
           by (rewrite (st_ok_restrict_reg SEGS (w_H W3) Ex ssy msn (Z_to_bv 5 (Z.of_nat 1)) HS2);
               replace (sr_get (ss_regs ssy) (Z_to_bv 5 (Z.of_nat 1))) with (SOff 240 14052)
                 by (vm_compute; reflexivity);
               cbn [sv_denot]; try rewrite EX240; rewrite (img_env_codeptr E HEI 14052); unfold w64; f_equal;
               unfold kpc, AF_kernel, KP_NLRET; lia);
         assert (Rr10 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 10)) = w64 (kW2 cx fpos))
           by (rewrite (st_ok_restrict_reg SEGS (w_H W3) Ex ssy msn (Z_to_bv 5 (Z.of_nat 10)) HS2);
               replace (sr_get (ss_regs ssy) (Z_to_bv 5 (Z.of_nat 10))) with (SOff 21 0)
                 by (vm_compute; reflexivity);
               cbn [sv_denot]; rewrite EX21, Z.add_0_r; reflexivity);
         assert (Rr12 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 12)) =
                        w64 (bv_unsigned (sv_denot Ex k2_ecut)))
           by (rewrite (st_ok_restrict_reg SEGS (w_H W3) Ex ssy msn (Z_to_bv 5 (Z.of_nat 12)) HS2);
               replace (sr_get (ss_regs ssy) (Z_to_bv 5 (Z.of_nat 12))) with k2_ecut
                 by (vm_compute; reflexivity);
               unfold w64; symmetry; apply Z_to_bv_bv_unsigned);
         apply (k2_fin POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 msn mdn c ci j m k n f adv adv'
                  (bv_unsigned (sv_denot Ex k2_ecut)) HC HB HJ1 HFR HRc HRm Hc Hci Hj Hm Hk
                  HW HAT HMSn
                  ltac:(apply (kregs0_keep cx ms1); [exact HK0 | exact HR01])
                  Rr1 Rr10 Rr12
                  ltac:(intros r Hr; rewrite (HKN r Hr); exact (HKN1 r Hr))
                  ltac:(repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfds1)
                  ltac:(repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfs1)
                  ltac:(intros a Ha Hna; rewrite HmB; exact (UN1 a Ha Hna))
                  ltac:(intros a Ha; rewrite HmB; exact (HP1 a Ha))
                  Hadv' ltac:(rewrite HmB; exact Hp1) ltac:(rewrite HmB; exact Hn1)
                  (bv_unsigned_in_range 64 (sv_denot Ex k2_ecut)) (k2_ecut_ok Ex cb EX12 Hcb))
       end.
Qed.

(* ---- STAGE 1, arm (A): no byte left (a3 = 0): +0x1178 -> +0x1b2c -> +0x1b30, nothing written ---- *)
Lemma k2_armA : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv,
  kfrom SK B POST (kin_ncall B Rc Rm) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K2 (k2_rl cx fpos m) (k2_sl cx fpos c ci m k) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 13)) = w64 (k_wn cx - adv) ->
  k_wn cx - adv = 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv
    HC HB HJ HFR HRc HRm Hc Hci Hj Hm Hk HW HAT Q13 Hz.
  pose proof HJ as HJ0.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & _ & HJB & HKK & HCUR & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HR0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  destruct HCUR as (Hadv0 & HCP & HCN & HCW).
  assert (R13 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 13)) = w64 0) by (rewrite Q13, Hz; reflexivity).
  remember (Eimg (Ereg (ms_regs ms3) (@nil word))) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (@nil word)) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hjr; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (E20 : ew E 20%nat = w64 SHADOW_OFF) by (rewrite (ER 20%nat 20%bv eq_refl); exact R20).
  assert (HS : st_ok_pi SEGS pa_val E k2_ssA (restrict (w_H W3) ms3)).
  { rewrite (kn_ms_shape ms3 (BASE + kpc KP_K2) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold k2_ssA. apply pa_entry_st_ok_full.
    - apply k2_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R13. cbn [sv_denot]. reflexivity.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint]. exact I.
    - unfold k2_fA, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; [exact I | exact I]].
      split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20. unfold w64.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
      split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
  assert (SHOK : sh_ok SEGS k2_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK k2_span (kpc KP_CODE).
  { apply awr_ok_x_nil. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?mq) |- _ => rename mq into ms2 end.
  repeat rewrite wvb_collapse in HJ.
  assert (Hmem : ms_mem ms2 = ms_mem ms3).
  { apply functional_extensionality. intros x.
    lazymatch goal with HFx : frame_of _ _ (ms_mem ms3) (ms_mem ms2) |- _ => apply HFx end.
    intros (rr & Hin & _). exact (False_ind _ Hin). }
  lazymatch goal with
  | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ms2) |- _ =>
    assert (HMS2 : kms KP_CODE ms2)
      by (apply (kn_kms_of _ E ssx ms2 KP_CODE HSx); vm_compute; reflexivity);
    assert (HK0 : forall r, In r nx_keep0 -> getr (ms_regs ms2) r = getr (ms_regs ms3) r)
      by exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) ms2) (ms_regs ms3) (@nil word) nx_keep0 HSx
                  HAG ltac:(vm_compute; reflexivity));
    assert (HKN : forall r, In r nx_keepN ->
              getr (ms_regs ms2) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr;
          exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) ms2) (ms_regs ms3) (@nil word)
                   (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) nx_keepN) HSx HAG
                   ltac:(vm_compute; reflexivity) _ (kn_in_map5 r nx_keepN Hr)));
    assert (QC : getr (ms_regs ms2) (Z_to_bv 5 (Z.of_nat 12)) = w64 0)
      by (rewrite (st_ok_pi_restrict_reg (w_H W3) E ssx ms2 (Z_to_bv 5 (Z.of_nat 12)) HSx);
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 12))) with (SLit 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; reflexivity);
    apply (k2_stage2 POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 ms2 _ c ci j m k n f adv adv 0
             HC HB HJ0 HJ HFR HRc HRm Hc Hci Hj Hm Hk HW HAT HMS2
             ltac:(apply (kregs0_keep cx ms3); [exact HK0 | exact HR0])
             HKN QC ltac:(lia)
             ltac:(repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
             ltac:(repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
             ltac:(intros a _ _; rewrite Hmem; reflexivity)
             ltac:(intros a Ha; rewrite Hmem; exact Ha)
             ltac:(lia) ltac:(rewrite Hmem; exact HCP) ltac:(rewrite Hmem; exact HCN))
  end.
Qed.

(* ---- STAGE 1, arm (B): one byte left: +0x1178 -> +0x11bc -> +0x1b30, the cursor advanced by one ---- *)
Lemma k2_armB : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv,
  kfrom SK B POST (kin_ncall B Rc Rm) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K2 (k2_rl cx fpos m) (k2_sl cx fpos c ci m k) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  1 <= adv ->
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 10)) = w64 (k_wp cx + adv) ->
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 11)) = w64 (k_wp cx + adv - 1) ->
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 12)) = w64 (k_wn cx - adv + 1) ->
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 13)) = w64 (k_wn cx - adv) ->
  k_wn cx - adv <> 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv
    HC HB HJ HFR HRc HRm Hc Hci Hj Hm Hk HW HAT Hadv1 Q10 Q11 Q12 Q13 Hnz.
  pose proof HJ as HJ0.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & HKK & HCUR & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HR0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  destruct HCUR as (Hadv0 & HCP & HCN & HCW).
  assert (Hlt : adv < k_wn cx) by lia.
  pose proof (kn_sp1 SK B cx HB) as (P1 & Pal & P3 & P4 & P5 & P6 & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & HAPW).
  destruct HAPW as (_ & _ & _ & HAPC). unfold apart in HAPC.
  change (aarg (k_regs cx) 0) with (ka0 cx) in HAPC.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hwpr & Hwnr & Hd & Hdl & _).
  assert (HardC : kernel_ard SEGS (k_regs cx) (km0 cx) (ka0 cx)) by (apply kn_ard_cur; lia).
  assert (HardC15 : kernel_ard SEGS (k_regs cx) (km0 cx) (ka0 cx + 15)) by (apply kn_ard_cur; lia).
  assert (HardI : kernel_ard SEGS (k_regs cx) (km0 cx) (k_wp cx + adv))
    by (apply (kn_ard_inp SK B cx (k_wp cx + adv) ltac:(lia) HB)).
  destruct (kn_rd_facts SK B LAWS cx fpos k2 ly3 S3 md3 (ka0 cx) HB HJB HardC) as (RC1 & RC2 & _).
  destruct (kn_rd_facts SK B LAWS cx fpos k2 ly3 S3 md3 (k_wp cx + adv) HB HJB HardI) as (RI1 & RI2 & _).
  destruct (kn_ard_bound SK B LAWS cx (ka0 cx) HB HardC) as (_ & RCW).
  destruct (kn_ard_bound SK B LAWS cx (ka0 cx + 15) HB HardC15) as (_ & RCW15).
  destruct (kn_ard_bound SK B LAWS cx (k_wp cx + adv) HB HardI) as (_ & RIW).
  rewrite HKA in RCW, RCW15, RIW.
  (* the input byte at the cursor, at this memory *)
  assert (Hin : (Z.to_nat adv < length (k_d cx))%nat) by lia.
  destruct (nth_error (k_d cx) (Z.to_nat adv)) as [bb|] eqn:Ebb;
    [|apply nth_error_None in Ebb; lia].
  destruct Hd as (Hd0 & Hd1 & Hdb).
  pose proof (Hdb (Z.to_nat adv) Hin) as Hdbi. rewrite Ebb in Hdbi.
  replace (k_wp cx + Z.of_nat (Z.to_nat adv)) with (k_wp cx + adv) in Hdbi by lia.
  destruct (kn_input_at SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 (k_wp cx + adv) HB HJ HJB HKK ltac:(lia))
    as (Hsd & Hvw).
  assert (Hmb3 : mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (k_wp cx + adv) = Some bb)
    by (rewrite <- Hdbi; unfold km0; apply mbyte_of_aview; exact Hvw).
  pose proof (bv_unsigned_in_range 8 bb) as Hbbr. change (bv_modulus 8) with 256 in Hbbr.
  pose proof (kn_slot_of cx W3 ms3 _ KS_CSH (shadow_of_addr SHADOW_OFF (ka0 cx)) HSL
    ltac:(unfold k2_sl; apply in_or_app; left; unfold kslots_setup; km_inl)) as SL_CSH.
  remember (Eimg (Ereg (ms_regs ms3) [w64 (bv_unsigned bb)])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) [w64 (bv_unsigned bb)]) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hjr; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (EXT : forall jn, (jn < 1)%nat -> ew E (32 + jn) = nth jn [w64 (bv_unsigned bb)] (Z_to_bv 64 0))
    by (intros jn Hjn; rewrite HEdef, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EXT 0%nat ltac:(lia)) as E32. cbn [nth Nat.add] in E32.
  assert (E9 : ew E 9%nat = w64 (ksp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact R9).
  assert (E18 : ew E 18%nat = w64 (ka0 cx)) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E20 : ew E 20%nat = w64 SHADOW_OFF) by (rewrite (ER 20%nat 20%bv eq_refl); exact R20).
  assert (E10 : ew E 10%nat = w64 (k_wp cx + adv))
    by (rewrite (ER 10%nat (Z_to_bv 5 (Z.of_nat 10)) eq_refl); exact Q10).
  assert (E11 : ew E 11%nat = w64 (k_wp cx + adv - 1))
    by (rewrite (ER 11%nat (Z_to_bv 5 (Z.of_nat 11)) eq_refl); exact Q11).
  assert (E12 : ew E 12%nat = w64 (k_wn cx - adv + 1))
    by (rewrite (ER 12%nat (Z_to_bv 5 (Z.of_nat 12)) eq_refl); exact Q12).
  assert (E13 : ew E 13%nat = w64 (k_wn cx - adv))
    by (rewrite (ER 13%nat (Z_to_bv 5 (Z.of_nat 13)) eq_refl); exact Q13).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (rewrite E18; apply unsigned_lit_small; lia).
  assert (BV10 : bv_unsigned (ew E 10%nat) = k_wp cx + adv)
    by (rewrite E10; apply unsigned_lit_small; lia).
  assert (BV20 : bv_unsigned (ew E 20%nat) = SHADOW_OFF)
    by (rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (BV32 : bv_unsigned (ew E 32%nat) = bv_unsigned bb)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (BV13 : bv_unsigned (ew E 13%nat) = k_wn cx - adv)
    by (rewrite E13; apply unsigned_lit_small; lia).
  assert (A21 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 21)) = w64 (kW2 cx fpos))
    by exact (kn_reg_in ms3 _ 21%nat _ HRL ltac:(unfold k2_rl; kn_in)).
  assert (A24 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 24)) = w64 (kS8 cx))
    by exact (kn_reg_in ms3 _ 24%nat _ HRL ltac:(unfold k2_rl; kn_in)).
  assert (A25 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 25)) = w64 (kW2 cx fpos + NW_N))
    by exact (kn_reg_in ms3 _ 25%nat _ HRL ltac:(unfold k2_rl; kn_in)).
  assert (A22 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 22)) = w64 m)
    by exact (kn_reg_in ms3 _ 22%nat _ HRL ltac:(unfold k2_rl; kn_in)).
  assert (E21 : ew E 21%nat = w64 (kW2 cx fpos))
    by (rewrite (ER 21%nat (Z_to_bv 5 (Z.of_nat 21)) eq_refl); exact A21).
  assert (E25 : ew E 25%nat = w64 (kW2 cx fpos + NW_N))
    by (rewrite (ER 25%nat (Z_to_bv 5 (Z.of_nat 25)) eq_refl); exact A25).
  assert (E22 : ew E 22%nat = w64 m)
    by (rewrite (ER 22%nat (Z_to_bv 5 (Z.of_nat 22)) eq_refl); exact A22).
  assert (HS : st_ok_pi SEGS pa_val E k2_ssB (restrict (w_H W3) ms3)).
  { rewrite (kn_ms_shape ms3 (BASE + kpc KP_K2) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold k2_ssB, k2_regs. apply pa_entry_st_ok_full.
    - apply k2_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      unfold k2_sh. rewrite (km_denot_sh E 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
      rewrite (kn_reg_in ms3 _ 24%nat (kS8 cx) HRL ltac:(unfold k2_rl; kn_in)).
      unfold kS8, shadow_of_addr. reflexivity.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      + unfold k2_rgS, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite BV9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc0 (k2_sh 18 0)
                 (shadow_of_addr SHADOW_OFF (ka0 cx))); [|exact SL_CSH].
        unfold k2_sh. rewrite (km_denot_sh E 18 (ka0 cx) 0 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
        unfold shadow_of_addr. rewrite Z.add_0_r. reflexivity.
      + unfold k2_rgCur, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite BV18.
        split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HCW o Ho)|]. apply Forall_nil.
      + unfold k2_rgIn, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite BV10.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (k_wp cx + adv) 0 1 (SOff 32 0) (bv_unsigned bb));
          [apply sv_off0; exact E32 | change (2 ^ (8 * Z.of_N 1)) with 256; lia
           | change (Z.of_N 1) with 1; lia |].
        rewrite Z.add_0_r. exact (k2_val1 SEGS _ _ bb Hmb3).
    - apply pairwise_disjoint_of_extents.
      unfold extent_of_region, k2_rgS, k2_rgCur, k2_rgIn.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite BV9, BV18, BV10.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    - unfold k2_fB, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite BV9, BV18, BV10, BV20, BV32, BV13.
      change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
      repeat split; first [lia | exact I | exact Pal]. }
  assert (SHOK : sh_ok SEGS k2_Bx k2_SHB E (mrestrict (w_H W3) (ms_mem ms3))).
  { unfold sh_ok, k2_SHB. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - exact (Forall_inv (km_shok SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 E HB HJ HJB HKK E18 E20)).
    - apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E k2_Bx 10%nat (k_wp cx + adv) 1
               (k_wp cx + adv) 0 1
               ltac:(apply ra_of_saddr; intros y Hy; replace y with (k_wp cx + adv) by lia; exact Hsd)
               ltac:(unfold k2_Bx; apply k2_U0; [exact BV20 | unfold SHADOW_OFF; lia]));
        [apply k2_U0; [exact BV10 | lia] | lia | lia |].
      intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia.
      replace y with (k_wp cx + adv) by lia. exact RI2. }
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK k2_span (kpc KP_CODE).
  { cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]]].
    - intros y Hy. cbn [k2_rgS YP09.r_base YP09.r_wlo YP09.r_whi] in Hy. lia.
    - intros y Hy. cbn [k2_rgCur YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy. rewrite BV18 in Hy.
      exact (k2_awr_cur cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ HJB y ltac:(lia)).
    - intros y Hy. cbn [k2_rgIn YP09.r_base YP09.r_wlo YP09.r_whi] in Hy. lia. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?mq) |- _ => rename mq into ms2 end.
  repeat rewrite wvb_collapse in HJ.
  lazymatch goal with
  | HFy : frame_of ?Ez ?rz (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ms2)) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) Ez rz (w_H W3) (ms_mem ms3) (ms_mem ms2)
      (fun a => ka0 cx <= a < ka0 cx + 16) HFy) as UN0
  end.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) ->
            aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hna. apply UN0; [|exact Ha|exact Hna].
    intros bq wlo whi y Hinw Hy. cbv beta. vm_compute in Hinw.
    destruct Hinw as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-; cbn [base_val] in Hy;
      [lia | rewrite BV18 in Hy; lia | lia]. }
  spregion HS 1%nat HRC.
  lazymatch goal with
  | HSx : st_ok_pi _ _ ?Ey ?ssx (restrict _ ms2) |- _ =>
    assert (EY18 : bv_unsigned (ew Ey 18%nat) = ka0 cx)
      by (first [exact BV18 | rewrite !k2_ew_set by lia; exact BV18]);
    assert (EY11 : ew Ey 11%nat = w64 (k_wp cx + adv - 1))
      by (first [exact E11 | rewrite !k2_ew_set by lia; exact E11]);
    assert (EY12 : ew Ey 12%nat = w64 (k_wn cx - adv + 1))
      by (first [exact E12 | rewrite !k2_ew_set by lia; exact E12]);
    assert (EY32 : ew Ey 32%nat = w64 (bv_unsigned bb))
      by (first [exact E32 | rewrite !k2_ew_set by lia; exact E32]);
    assert (EYA : env_agree 32 (Ereg (ms_regs ms3) [w64 (bv_unsigned bb)]) Ey)
      by (split; [intros qa Hqa; rewrite ?k2_ew_set by lia; exact (proj1 HAG qa Hqa)
                 | exact (proj2 HAG)]);
    assert (DP : sv_denot Ey (SOff 11 2) = Z_to_bv 64 (k_wp cx + (adv + 1)))
      by (cbn [sv_denot]; rewrite EY11; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia);
    assert (DN : sv_denot Ey (SOff 12 (-2)) = Z_to_bv 64 (k_wn cx - (adv + 1)))
      by (cbn [sv_denot]; rewrite EY12; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia);
    pose proof (field_of_region (segs := SEGS) Ey _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 11 2) _ HRC EY18
                  ltac:(km_inl) DP ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
                  ltac:(change (Z.of_N 8) with 8; lia)) as VP;
    pose proof (field_of_region (segs := SEGS) Ey _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SOff 12 (-2)) _ HRC EY18
                  ltac:(km_inl) DN ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
                  ltac:(change (Z.of_N 8) with 8; lia)) as VN;
    rewrite Z.add_0_r in VP;
    assert (HMS2 : kms KP_CODE ms2)
      by (apply (kn_kms_of _ Ey ssx ms2 KP_CODE HSx); vm_compute; reflexivity);
    assert (HK0 : forall r, In r nx_keep0 -> getr (ms_regs ms2) r = getr (ms_regs ms3) r)
      by exact (regs_kept_of_st_ok_pi Ey ssx (restrict (w_H W3) ms2) (ms_regs ms3)
                  [w64 (bv_unsigned bb)] nx_keep0 HSx EYA ltac:(vm_compute; reflexivity));
    assert (HKN : forall r, In r nx_keepN ->
              getr (ms_regs ms2) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr; unfold nx_keepN in Hr; cbn [In] in Hr;
          destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
          rewrite (st_ok_pi_restrict_reg (w_H W3) Ey ssx ms2 _ HSx);
          [ replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 21))) with (SOff 21 0)
              by (vm_compute; reflexivity);
            rewrite A21; apply sv_off0; exact E21
          | replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 24))) with (k2_sh 18 8)
              by (vm_compute; reflexivity);
            rewrite A24; unfold k2_sh;
            rewrite (km_denot_sh Ey 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20);
            unfold kS8, shadow_of_addr; reflexivity
          | replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 25))) with (SOff 25 0)
              by (vm_compute; reflexivity);
            rewrite A25; apply sv_off0; exact E25
          | replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 22))) with (SOff 22 0)
              by (vm_compute; reflexivity);
            rewrite A22; apply sv_off0; exact E22 ]);
    assert (QC : getr (ms_regs ms2) (Z_to_bv 5 (Z.of_nat 12)) = w64 (bv_unsigned bb))
      by (rewrite (st_ok_pi_restrict_reg (w_H W3) Ey ssx ms2 (Z_to_bv 5 (Z.of_nat 12)) HSx);
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 12))) with (SOff 32 0)
            by (vm_compute; reflexivity);
          apply sv_off0; exact EY32);
    apply (k2_stage2 POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 ms2 _ c ci j m k n f adv (adv + 1)
             (bv_unsigned bb) HC HB HJ0 HJ HFR HRc HRm Hc Hci Hj Hm Hk HW HAT HMS2
             ltac:(apply (kregs0_keep cx ms3); [exact HK0 | exact HR0])
             HKN QC ltac:(lia)
             ltac:(repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
             ltac:(repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
             UN
             ltac:(intros a Ha; exact (apresent_grows _ _ _ a HG Ha))
             ltac:(lia) VP VN)
  end.
Qed.

(* ---- THE PHASE: kind 2 ---- *)
Theorem kn_k2 : forall POST (Rc Rm : kcx -> Z -> Prop),
  kfrom SK B POST (kin_next B Rc Rm) -> kfrom SK B POST (kin_kind B Rc Rm 2).
Proof.
  intros POST Rc Rm HN.
  pose proof (kn_ncall SK B LAWS LV KI ANLERR POST Rc Rm HN) as HC.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (c & ci & j & m & k & n & f & adv & HRc & HRm & Hc & Hci & Hj & Hm & Hk & _ & HW & HD & HAT).
  change (kind_pc 2) with KP_K2 in HAT.
  destruct HD as [Hbad | (Hadv1 & HQ)]; [lia|].
  unfold kregs_eq in HQ. rewrite !Forall_cons_iff in HQ.
  destruct HQ as (Q10 & Q11 & Q12 & Q13 & _). cbn [fst snd] in Q10, Q11, Q12, Q13.
  destruct (Z.eq_dec (k_wn cx - adv) 0) as [Hz | Hnz].
  - exact (k2_armA POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv
             HC HB HJ HFR HRc HRm Hc Hci Hj Hm Hk HW HAT Q13 Hz).
  - exact (k2_armB POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv
             HC HB HJ HFR HRc HRm Hc Hci Hj Hm Hk HW HAT Hadv1 Q10 Q11 Q12 Q13 Hnz).
Qed.

End b.
End a.

Print Assumptions kn_k2.
