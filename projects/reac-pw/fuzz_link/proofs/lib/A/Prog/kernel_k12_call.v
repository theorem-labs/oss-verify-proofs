(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its module names changed; 244 of its 330 lines of code are new or changed and 400 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the call of nl_error at +0x1b7c that
   ends the messages of kinds 1 and 2, and the one instruction after it. Listing
   (internal path) (internal record, sha256 7bc02d6772b3), +0x1b7c .. +0x1b84.

   THE CUT AT THE CALL (kin_ncall). Both kinds reach `jal nl_error` (+0x1b7c) with a0 = s5 = w2, a1 the error code
   (nl_error's Pre leaves it free) and a2 = the cut, which is 0..7 or 2 ^ 64 - 1 and so meets nl_error's premise
   `a2 <= NL_ERR_BODY \/ 2 ^ 63 <= a2`. The engine stops the run at the call (PTS_call LS_nl_error) with the pc set
   to nl_error's entry 0x86e4c = BASE + kpc KP_NLERR and ra = BASE + kpc KP_NLRET, so the cut of this file sits at
   the callee's entry.

   THE CALL. lib/A/Prog/kernel_ocall.v `kn_ocall` is the own-callee step: it takes the callee's contract as an
   `aleaf_rd` whose write set is w2 and whose Post keeps w2 a struct nl_w whose n only grows, and continues at the
   return with the cut rebuilt. nl_error_c.v's `nl_error_acontract` is an `aleaf` (no read set): link_amem.v
   `aleaf_rd_none` turns it into the `aleaf_rd` with Rd = False, and SIDE = [(1, 1)] is kernel_ocall.v's
   `kn_side_room1`. nl_error's Pre at the cut is `k12_nlerr_pre`: w2's bytes from `kw_at` (LinkWalkNlw
   anlw_of_nlw_fields), its separation from kernel's window and its place in the application memory from F's
   geometry (kernel_kit.v kn_F_facts, kn_sp1), its shadow from F's shadow bytes (kn_w2_ra for the addressability,
   the 0x220..0x428 run of `kfsh` for the hull).

   THE RETURN. +0x1b80 `ld a4, 0xa0(s1)` reloads k from the spill slot KS_K and +0x1b84 is kin_next. One run with a
   single read-only region (the slot) and no shadow entry (the load is not instrumented); the run writes nothing, so
   the cut moves by kernel_next.v `kat_move` and w2's fields are the callee's Post's.

   Callees: nl_error (ANLERR). Section hypotheses used: LAWS, LV, KI (kn_ocall's), ANLERR.
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
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_error_c kernel_c kernel_img kernel_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalkCall PcapRelro kernel_kit kernel_entry kernel_next kernel_ocall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* nl_error's entry and the return, as kpc offsets: BASE + kpc KP_NLERR = 0x86e4c, BASE + kpc KP_NLRET = 0x858b0 *)
Definition KP_NLERR : Z := 0x311c.
Definition KP_NLRET : Z := 0x1b80.

(* ---- the symbolic state at +0x1b80: the spill slot KS_K read-only, no shadow entry ---- *)
Definition k12_Bx : sv := SOff 20 0.
Definition k12_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition k12_rgK : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xa0 0xa8 0 0 [YP09.mkChunk 0xa0 (CVal 8 (SOff 32 0))].
Definition k12_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition k12_ssR : sstate := mkSS (kpc KP_NLRET) sr_atoms [k12_rgK] None k12_facts.

(* a cut register, at a bitvector index the engine's lemmas give *)
Lemma k12_getr : forall (ms : machine_state) rl (r : nat) (b : bv 5) v,
  kregs_eq ms rl -> In (r, v) rl -> Z.of_nat r = bv_unsigned b -> getr (ms_regs ms) b = w64 v.
Proof.
  intros ms rl r b v H Hin Hb.
  replace b with (Z_to_bv 5 (Z.of_nat r)).
  - exact (kn_reg_in ms rl r v H Hin).
  - apply bv_eq. rewrite Z_to_bv_unsigned, Hb. apply bv_wrap_small. apply bv_unsigned_in_range.
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
Hypothesis ANLERR : nl_error_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

(* ---- THE CUT AT nl_error's ENTRY ---- *)
Definition kin_ncall (Rc Rm : kcx -> Z -> Prop)
  : kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv cut,
    Rc cx (c - ci) /\ Rm cx (m - k) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
    1 <= m <= 5 /\ 0 <= k < m /\
    0 <= cut < 2 ^ 64 /\ (cut <= NL_ERR_BODY \/ 2 ^ 63 <= cut) /\
    kw_at W3 ms3 (kW2 cx fpos) n f /\
    kat B cx fpos KP_NLERR
      [(1%nat, BASE + kpc KP_NLRET); (10%nat, kW2 cx fpos); (12%nat, cut);
       (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, m)]
      (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
      (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* the registers kn_ocall keeps across the call: the callee-saved ones of the cut *)
Definition k12_rlR (cx : kcx) (fpos m : Z) : list (nat * Z) :=
  [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, m)].

(* ---- nl_error's contract, as the aleaf_rd kn_ocall takes ---- *)
Lemma k12_leaf :
  aleaf_rd SK SEGS PCAP_RLO PCAP_RHI B NL_ERROR_A NL_ERROR_AK 0 [(1, 1)]
    (nl_error_apre SEGS) (fun _ _ _ => False) kn_wawr kn_wpost.
Proof. apply aleaf_rd_none. exact ANLERR. Qed.

(* ---- nl_error's Pre at the cut ---- *)
Lemma k12_nlerr_pre : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 n f,
  kbase SK B cx ->
  kjbk B cx fpos k2 ly3 S3 md3 ->
  kshadow cx fpos W3 ms3 (kfsh 0xf8 0 0xf3) ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  aarg (ms_regs ms3) 0 = kW2 cx fpos ->
  spZ (ms_regs ms3) = ksp1 cx ->
  (aarg (ms_regs ms3) 2 <= NL_ERR_BODY \/ 2 ^ 63 <= aarg (ms_regs ms3) 2) ->
  nl_error_apre SEGS (ms_regs ms3) (rdW W3 (ms_mem ms3)).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 n f HB HJB HSH HW Ha0 Hsp Hcut.
  destruct (anlw_of_nlw_fields SEGS _ _ _ _ HW) as (bs & Hbs & Hwf & _ & _).
  pose proof (kn_sp SK B cx HB) as (G1 & G2 & _ & G4 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HRA.
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity.
  assert (HNK : NL_ERROR_AK = 4272) by reflexivity.
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  rewrite Hfb in F2, F3.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  assert (HFS : kFSH cx fpos = SHADOW_OFF + kF cx fpos / 8) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  unfold nl_error_apre. exists bs. rewrite Ha0.
  split; [exact Hbs|]. split; [exact Hwf|].
  split.
  { unfold apart_frame. rewrite Hsp. left. unfold NW_SIZE. lia. }
  split; [exact Hcut|].
  split.
  { unfold amem_range, kLowMemEnd, kHighMemEnd, NW_SIZE. unfold kHighMemBeg in *. lia. }
  split; [exact HRA|].
  (* shadow_hull_vis: the hull of w2's shadow is inside F's 0x448 shadow bytes *)
  assert (HSA : forall x, kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE ->
            kFSH cx fpos + 0x226 <= shadow_addr x <= kFSH cx fpos + 0x427).
  { intros x Hx. rewrite HFS. unfold shadow_addr. unfold NW_SIZE in Hx. lia. }
  intros s Hs.
  change (ard SEGS (mrestrict (w_H W3) (ms_mem ms3)) s)
    with (aview SEGS (w_H W3) (ms_mem ms3) s).
  pose proof (HSA (kW2 cx fpos) ltac:(unfold NW_SIZE; lia)) as Q1.
  pose proof (HSA (kW2 cx fpos + NW_SIZE - 1) ltac:(unfold NW_SIZE; lia)) as Q2.
  assert (HF8 : kFSH cx fpos mod 8 = 0) by (rewrite HFS; unfold SHADOW_OFF; lia).
  assert (Hi : 0x220 <= s - kFSH cx fpos < 0x428) by lia.
  unfold kshadow in HSH.
  replace s with (kFSH cx fpos + Z.of_nat (Z.to_nat (s - kFSH cx fpos))) by (rewrite Z2Nat.id; lia).
  rewrite (HSH (Z.to_nat (s - kFSH cx fpos))) by (rewrite kfsh_length; lia). discriminate.
Qed.

(* ---- engine helpers for the return step (kernel_k3.v's, at this file's state) ---- *)
Lemma k12_rdword_range : forall (H : word -> bool) (m : word -> option byte) a v,
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

Lemma k12_chunk_rd : forall E (H : word -> bool) (mm : word -> option byte) base off e v,
  sv_denot E e = Z_to_bv 64 v -> rdword (aview SEGS H mm) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H mm) base (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E H mm base off e v He Hr.
  pose proof (k12_rdword_range H mm (base + off) v Hr) as Hv.
  apply (chunk_ok_val SEGS E (mrestrict H mm) base off 8 e v He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
  - exact (val_mem_of_rdword SEGS H mm (base + off) v Hr).
Qed.

(* the fixed fields of a cut, off a state the engine stopped at a call (the pc is the callee's entry) *)
Lemma k12_kms_of : forall (H : word -> bool) E ss (ms : machine_state) (pc : Z),
  st_ok SEGS E ss (restrict H ms) -> ss_resv ss = None -> ss_pc ss = BASE + kpc pc -> kms pc ms.
Proof.
  intros H E ss ms pc HS Hrv Hpc.
  pose proof (st_ok_restrict_mkst SEGS H E ss ms HS Hrv) as Hsh. rewrite Hpc in Hsh.
  unfold kms. rewrite Hsh. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
  do 5 (split; [reflexivity|]). reflexivity.
Qed.

(* nl_error's entry, as the engine's `pa_sigma` gives it *)
Lemma k12_sigma_nlerr : pa_sigma LS_nl_error = BASE + kpc KP_NLERR.
Proof. rewrite pa_sigma_nl_error. unfold kpc, AF_kernel, KP_NLERR, AF_nl_error. lia. Qed.

(* ---- THE RETURN: +0x1b80 -> kin_next (+0x1b84) ---- *)
Lemma k12_ret : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly4 S4 W4 (ms4 : machine_state) md4
    c ci j m k n f adv,
  kfrom SK B POST (kin_next B Rc Rm) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly4 S4 W4 (ms_mem ms4) md4 k2 ->
  frames S4 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m ->
  kw_at W4 ms4 (kW2 cx fpos) n f ->
  kat B cx fpos KP_NLRET (k12_rlR cx fpos m)
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly4 S4 W4 ms4 md4 ->
  SRr SEGS W4 (mkCfg ms4 md4) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly4 S4 W4 ms4 md4 c ci j m k n f adv HN HB HJ HFR HRc HRm Hc Hci Hj Hm Hk HW HAT.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & HSL & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & Hal & Hlo & _ & _ & Hsp47 & _).
  pose proof (kn_sp SK B cx HB) as (Hac & Hsp2 & _ & Hs1 & _).
  pose proof HR0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  pose proof (kn_slot_of cx W4 ms4 _ KS_K k HSL ltac:(apply in_or_app; right; kn_in)) as SL_K.
  remember (Eimg (Ereg (ms_regs ms4) [w64 k])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms4) [w64 k]) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms4) r)
    by (intros jn r Hjr; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (EXT : forall jn, (jn < 1)%nat -> ew E (32 + jn) = nth jn [w64 k] (Z_to_bv 64 0))
    by (intros jn Hjn; rewrite HEdef, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EXT 0%nat ltac:(lia)) as E32. cbn [nth Nat.add] in E32.
  assert (B9 : bv_unsigned (ew E 9%nat) = ksp1 cx)
    by (rewrite (ER 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (B20 : bv_unsigned (ew E 20%nat) = SHADOW_OFF)
    by (rewrite (ER 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (B32 : bv_unsigned (ew E 32%nat) = k) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact B9.
  assert (HS : st_ok_pi SEGS pa_val E k12_ssR (restrict (w_H W4) ms4)).
  { rewrite (kn_ms_shape ms4 (BASE + kpc KP_NLRET) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold k12_ssR. apply pa_entry_st_ok_full.
    - rewrite HEdef. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold k12_rgK, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (k12_chunk_rd E (w_H W4) (ms_mem ms4) (ksp1 cx) 0xa0 (SOff 32 0) k); [|exact SL_K].
      cbn [sv_denot]. rewrite B32, Z.add_0_r. reflexivity.
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - unfold k12_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; [exact I | exact I]].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B9, B20.
      split.
      + split; [lia|]. split; [change (2 ^ 5) with 32; exact Hal | lia].
      + split; [|exact I]. split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
  assert (SHOK : sh_ok SEGS k12_Bx (@nil shent) E (mrestrict (w_H W4) (ms_mem ms4))) by apply Forall_nil.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK k12_span (kpc KP_NEXT).
  { cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold k12_rgK in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia. }
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms4) (ms_mem ?msn)
    |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    assert (Hmem : ms_mem msn = ms_mem ms4)
      by (apply functional_extensionality; intros x; apply HF';
          intros (rr & Hin & Hw); cbn [ss_mem In] in Hin; destruct Hin as [<-|[]];
          unfold k12_rgK in Hw; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia);
    assert (HMS' : kms KP_NEXT msn)
      by (apply (kn_kms_of _ E ssx msn KP_NEXT HS'); vm_compute; reflexivity);
    assert (HR0' : kregs0 cx msn)
      by (apply (kregs0_keep cx ms4 msn); [|exact HR0];
          exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W4) msn) (ms_regs ms4) [w64 k] nx_keep0 HS' HAG
                   ltac:(vm_compute; reflexivity)));
    assert (HKN : forall r, In r nx_keepN ->
              getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms4) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr;
          exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W4) msn) (ms_regs ms4) [w64 k]
                   (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) nx_keepN) HS' HAG
                   ltac:(vm_compute; reflexivity) _ (kn_in_map5 r nx_keepN Hr)));
    assert (H14 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 14)) = w64 k)
      by (rewrite (st_ok_pi_restrict_reg (w_H W4) E ssx msn (Z_to_bv 5 (Z.of_nat 14)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 14))) with (SOff 32 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity);
    assert (Hfds : m_fds mdn = m_fds md4) by exact (proj1 (wvb_fds_fs _ _ _));
    assert (Hfs : m_fs mdn = m_fs md4) by exact (proj2 (wvb_fds_fs _ _ _));
    apply (HN cx fpos k2 ly4 S4 W4 msn mdn HB ltac:(assumption) HFR)
  end.
  exists c, ci, j, m, k, n, f, adv.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hm|]. split; [exact Hk|].
  split; [unfold kw_at in *; rewrite Hmem; exact HW|].
  eapply kat_move;
    [ exact HAT | exact HMS' | exact HR0' | | exact Hmem | | exact Hfds | exact Hfs ].
  - unfold kregs_eq, k12_rlR in HRL |- *. rewrite !Forall_cons_iff in HRL.
    destruct HRL as (Q21 & Q24 & Q25 & Q22 & _). cbn [fst snd] in Q21, Q24, Q25, Q22.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + rewrite HKN by (unfold nx_keepN; kn_in). exact Q21.
    + rewrite HKN by (unfold nx_keepN; kn_in). exact Q24.
    + rewrite HKN by (unfold nx_keepN; kn_in). exact Q25.
    + exact H14.
    + rewrite HKN by (unfold nx_keepN; kn_in). exact Q22.
  - intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact Hx|].
    right. cbn [In] in Hx |- *. tauto.
Qed.

(* ---- THE PHASE: the call and the step after it ---- *)
Theorem kn_ncall : forall POST (Rc Rm : kcx -> Z -> Prop),
  kfrom SK B POST (kin_next B Rc Rm) -> kfrom SK B POST (kin_ncall Rc Rm).
Proof.
  intros POST Rc Rm HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (c & ci & j & m & k & n & f & adv & cut & HRc & HRm & Hc & Hci & Hj & Hm & Hk & Hcut0 & Hcutb &
    HW & HAT).
  pose proof HAT as (_ & HR0 & HRL & _ & _ & HSH & _ & HJB & _).
  pose proof HR0 as (R2 & _).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & _ & Hlo & _ & _ & Hsp47 & _).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity.
  assert (HNK : NL_ERROR_AK = 4272) by reflexivity.
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity. rewrite Hfb in F2.
  assert (Ha0 : aarg (ms_regs ms3) 0 = kW2 cx fpos).
  { unfold aarg, argZ. transitivity (bv_unsigned (getr (ms_regs ms3) 10)); [reflexivity|].
    rewrite (k12_getr ms3 _ 10%nat 10%bv (kW2 cx fpos) HRL ltac:(kn_in) eq_refl).
    unfold w64. apply unsigned_lit_small. unfold kW2, KN_W2. lia. }
  assert (Ha2 : aarg (ms_regs ms3) 2 = cut).
  { unfold aarg, argZ. transitivity (bv_unsigned (getr (ms_regs ms3) 12)); [reflexivity|].
    rewrite (k12_getr ms3 _ 12%nat 12%bv cut HRL ltac:(kn_in) eq_refl).
    unfold w64. apply unsigned_lit_small. lia. }
  assert (Hsp : spZ (ms_regs ms3) = ksp1 cx).
  { unfold spZ. transitivity (bv_unsigned (w64 (ksp1 cx))); [f_equal; exact R2|].
    unfold w64. apply unsigned_lit_small. lia. }
  eapply kn_ocall with (pcE := NL_ERROR_A) (K := NL_ERROR_AK) (SIDE := [(1, 1)])
                       (Pre := nl_error_apre SEGS) (Rd := fun _ _ _ => False)
                       (pc := KP_NLERR) (ret := KP_NLRET) (rl' := k12_rlR cx fpos m) (n := n) (f := f).
  - exact LAWS.
  - exact LV.
  - exact KI.
  - exact k12_leaf.
  - exact HB.
  - exact HJ.
  - exact HFR.
  - exact HAT.
  - exact HW.
  - rewrite (lv_text LV). unfold link_text, kpc, AF_kernel, KP_NLERR, NL_ERROR_A. lia.
  - lia.
  - eapply kn_side_room1; [exact HB | exact HFR].
  - exact (k12_getr ms3 _ 1%nat 1%bv (BASE + kpc KP_NLRET) HRL ltac:(kn_in) eq_refl).
  - unfold kpc, AF_kernel, KP_NLRET. lia.
  - unfold kpc, AF_kernel, KP_NLRET. lia.
  - exact (k12_getr ms3 _ 10%nat 10%bv (kW2 cx fpos) HRL ltac:(kn_in) eq_refl).
  - exact (k12_nlerr_pre cx fpos k2 ly3 S3 W3 ms3 md3 n f HB HJB HSH HW Ha0 Hsp ltac:(rewrite Ha2; exact Hcutb)).
  - intros a [].
  - unfold k12_rlR. intros x Hx. cbn [In] in Hx |- *. tauto.
  - unfold k12_rlR. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      unfold acallee_saved; do 5 right; lia.
  - reflexivity.
  - rewrite kfsh_length. lia.
  - intros ly4 S4 W4 ms4 md4 n' f' HJ4 HF4 HK4 HW4 Hle.
    exact (k12_ret POST Rc Rm cx fpos k2 ly4 S4 W4 ms4 md4 c ci j m k n' f' adv HN HB HJ4 HF4 HRc HRm Hc Hci Hj
             Hm Hk HW4 HK4).
Qed.

End b.
End a.

Print Assumptions kn_ncall.
