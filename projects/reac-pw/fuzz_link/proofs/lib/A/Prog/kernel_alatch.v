(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its addresses changed; 872 of its 1084 lines of code are new or changed and 274 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the attribute loop's latch of kinds 0, 7
   (lib/A/Prog/kernel_defs.v kin_alat, +0xb44) and nl_end (kin_nlend, +0x106c) to the cut after a message (kin_next,
   +0x1b84). Listing (internal path) (internal record, sha256 7bc02d6772b3), +0xb44 .. +0xb4c
   and +0x106c .. +0x1298, +0x1b80.

   kn_alatch (+0xb44): `addiw s6, s6, -1; bnez s6, +0x9d8; j +0x106c`. No memory access. The state pins s6 to the
   literal `left` (1..4, one run each): left >= 2 runs to kin_attr with left - 1, left = 1 to kin_nlend. The memory is
   the cut's (no window), so kernel_kit.v kat_frame_w2 with the empty range moves the cut.

   kn_nlend (+0x106c): a3 = n, a6 = hd (slot 0x90), a1 = hd + 4, s6 = m (slot 0x68). When n >= hd + 4 the length
   word n - hd is put at w2 + hd (+0x1080 .. +0x10c4). Kind 7 (slot 0x88) with n a multiple of 4 skips the pad: with
   n < 4096 one 0 byte is put at w2 + n and n += 1 (+0x1230), with n = 4096 full := 1 (+0x10f0); then (+0x1244) when
   the new n >= hd + 4 the length word is put again at w2 + hd, and a4 = k (+0x1248 / +0x1b80). Else (kind 0, or
   kind 7 with n not a multiple of 4) nl_pad at +0x1100: kernel_a5.v's (B) phase with the end +0x1b84 and a4 = k.
   A PRIVATE CUT at +0x1100 (al_pad: s6 = m). Two phases:
   (NA) al_nla: +0x106c -> +0x1100 / +0x1b84. The state: registers sr_atoms but s9 = w2 + 4096; atoms 32 = n,
   33 = full, 34 = w2 + n, 35 = k, 36 = hd, 37 = w2 + hd, 38 = m (al_ext); the slots 0x68 .. 0xc8 (al_sp), w2's two
   fields, the length word's 4 bytes at w2 + hd (b37) and the byte at w2 + n (b34) as regions; the aliases
   w2 + n = nt (atom 34, or w2 + hd + 3 when n + 1 = hd + 4) and w2 + hd = atom 37. The branches the engine cannot
   decide from the ranges are in the facts' conditions (n vs hd + 4, n vs (n + 3) & ~3, n >> 12 = 0), each true by an
   al_*_ok lemma. Nine arms by kind, n vs hd + 4, n mod 4, n = 4096, n + 1 vs hd + 4: ONE run each.
   (NB) al_padl: +0x1100 -> +0x1b84: as kernel_a5.v a5_padl (a run; or a run, checked_memset (a5_call_ms), a run).

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
kernel_c kernel_defs kernel_kit kernel_next kernel_k3 kernel_a5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition KP_PADN : Z := 0x1100.   (* nl_pad of kinds 0, 7: `ld a0, 0(s9)` *)

(* ---- the latch's state: s6 pinned ---- *)
Definition alL_ss (l : Z) : sstate :=
  mkSS (kpc KP_ALAT) (sr_set sr_atoms (Z_to_bv 5 (Z.of_nat 22)) (SLit l)) [] None (mkFacts [] [] []).

(* ---- (NA) the state at +0x106c ---- *)
Definition al_sp (kd : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x68 0xd0 0 0
    [YP09.mkChunk 0x68 (CVal 8 (SOff 38 0)); YP09.mkChunk 0x88 (CVal 8 (SLit kd));
     YP09.mkChunk 0x90 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x98 (CVal 8 (SLit 0xfffffffc));
     YP09.mkChunk 0xa0 (CVal 8 (SOff 35 0)); YP09.mkChunk 0xa8 (CVal 8 (SLit 4097));
     YP09.mkChunk 0xc8 (CVal 8 (SOff 21 4104))].
Definition al_hr : YP09.region := YP09.mkRegion (Some 37%nat) 0 4 0 4 [].
Definition al_nr : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 1 [].
Definition al_ws (b37 b34 : bool) : list YP09.region :=
  (if b37 then [al_hr] else []) ++ (if b34 then [al_nr] else []).
Definition al_atoms (nlo nhi : Z) : list (nat * afact) :=
  [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (21%nat, mkAF 4096 (2 ^ 47 - 4113) 0);
   (32%nat, mkAF nlo nhi 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 4096 (2 ^ 47 - 4113) 0);
   (36%nat, mkAF 0 4096 0); (37%nat, mkAF 4096 (2 ^ 47 - 4113) 0)].
Definition al_alias (nt : sv) : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 21 0) (SOff 32 0), nt); (SAlu ALU_ADD (SOff 21 0) (SOff 36 0), SOff 37 0)].
Definition al_ss (kd nlo nhi : Z) (b37 b34 : bool) (nt : sv) (cs : list acond) : sstate :=
  mkSS (kpc KP_NLEND) k3_regs (al_sp kd :: k3_fl :: al_ws b37 b34) None (mkFacts (al_atoms nlo nhi) cs (al_alias nt)).
Definition al_SH (b37 b34 : bool) : list shent :=
  mkSHE 21 4096 4112 :: (if b37 then [mkSHE 37 0 11] else []) ++ (if b34 then [mkSHE 34 0 8] else []).

(* the conditions: n + c vs hd + 4 (+0x107c, +0x124c), n vs (n + 3) & ~3 (+0x10e4), n >> 12 = 0 (+0x10ec) *)
Definition al_lt (c : Z) : acond := mkAC BC_LTU (SOff 32 c) (SOff 36 4).
Definition al_ge (c : Z) : acond := mkAC BC_GEU (SOff 32 c) (SOff 36 4).
Definition al_ne : acond := mkAC BC_NE (SOff 32 0) (a5_and 3).
Definition al_eq : acond := mkAC BC_EQ (SOff 32 0) (a5_and 3).
Definition al_srl : acond := mkAC BC_EQ (SAlu ALU_SRL (SOff 32 0) (SLit 12)) (SLit 0).

Lemma al_lt_ok : forall E n hd c, bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 36) = hd ->
  0 <= n + c < 2 ^ 47 -> 0 <= hd <= 4096 -> n + c < hd + 4 -> acond_ok E (al_lt c).
Proof.
  intros E n hd c Hn Hh H1 H2 H3. unfold acond_ok, al_lt. cbn [ac_c ac_a ac_b].
  rewrite branch_ltu_U, !U_SOff, Hn, Hh.
  rewrite (zcanon_id (n + c)), (zcanon_id (hd + 4)) by (unfold M64; lia). apply Z.ltb_lt. lia.
Qed.

Lemma al_ge_ok : forall E n hd c, bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 36) = hd ->
  0 <= n + c < 2 ^ 47 -> 0 <= hd <= 4096 -> hd + 4 <= n + c -> acond_ok E (al_ge c).
Proof.
  intros E n hd c Hn Hh H1 H2 H3. unfold acond_ok, al_ge. cbn [ac_c ac_a ac_b].
  rewrite branch_geu_U, !U_SOff, Hn, Hh.
  rewrite (zcanon_id (n + c)), (zcanon_id (hd + 4)) by (unfold M64; lia).
  apply negb_true_iff, Z.ltb_ge. lia.
Qed.

Lemma al_ne_ok : forall E n, bv_unsigned (ew E 32) = n -> 0 <= n <= 4096 -> n mod 4 <> 0 -> acond_ok E al_ne.
Proof.
  intros E n Hn H Hm. unfold acond_ok, al_ne, a5_and. cbn [ac_c ac_a ac_b].
  rewrite branch_ne_U, U_SOff, Hn. rewrite (a5_U_and E n 3 Hn) by lia.
  rewrite (zcanon_id (n + 0)) by (unfold M64; lia). apply negb_true_iff, Z.eqb_neq. lia.
Qed.

Lemma al_eq_ok : forall E n, bv_unsigned (ew E 32) = n -> 0 <= n <= 4096 -> n mod 4 = 0 -> acond_ok E al_eq.
Proof.
  intros E n Hn H Hm. unfold acond_ok, al_eq, a5_and. cbn [ac_c ac_a ac_b].
  rewrite branch_eq_U, U_SOff, Hn. rewrite (a5_U_and E n 3 Hn) by lia.
  rewrite (zcanon_id (n + 0)) by (unfold M64; lia). apply Z.eqb_eq. lia.
Qed.

Lemma al_srl_ok : forall E n, bv_unsigned (ew E 32) = n -> 0 <= n < 4096 -> acond_ok E al_srl.
Proof.
  intros E n Hn H. unfold acond_ok, al_srl. cbn [ac_c ac_a ac_b].
  rewrite branch_eq_U, U_SAlu, U_SOff, !U_SLit, Hn. cbn [zalu_raw].
  rewrite (zcanon_id (n + 0)) by (unfold M64; lia).
  change (Z.land (zcanon 12) 63) with 12. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by lia. reflexivity.
Qed.

Ltac al_conds B32 B36 :=
  cbn [conds_ok]; repeat split;
  first [ exact I
        | eapply al_lt_ok; [exact B32 | exact B36 | lia | lia | lia]
        | eapply al_ge_ok; [exact B32 | exact B36 | lia | lia | lia]
        | eapply al_ne_ok; [exact B32 | lia | lia]
        | eapply al_eq_ok; [exact B32 | lia | lia]
        | eapply al_srl_ok; [exact B32 | lia] ].

(* the windows of (NA)'s state lie in w2 *)
Lemma al_windows : forall (E : env) kd nlo nhi b37 b34 nt cs w n hd,
  base_val E (Some 21%nat) = w -> base_val E (Some 34%nat) = w + n -> base_val E (Some 37%nat) = w + hd ->
  0 <= n -> n + 1 <= 4112 -> 0 <= hd -> hd + 4 <= 4112 ->
  forall b wlo whi a, In (b, wlo, whi) (windows (ss_mem (al_ss kd nlo nhi b37 b34 nt cs))) ->
    base_val E b + wlo <= a < base_val E b + whi -> w <= a < w + NW_SIZE.
Proof.
  intros E kd nlo nhi b37 b34 nt cs w n hd H21 H34 H37 Hn Hn1 Hh Hh4 b wlo whi a Hin Ha.
  unfold al_ss, windows in Hin. unfold NW_SIZE.
  destruct b37, b34;
    cbn [ss_mem map In al_ws app al_sp k3_fl al_hr al_nr YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-;
      first [lia | rewrite H21 in Ha; lia | rewrite H34 in Ha; lia | rewrite H37 in Ha; lia] |]);
    destruct Hin.
Qed.

(* ---- (NB) the state at +0x1100: the slots 0x98 (the mask), 0xa0 (k), 0xa8 (4097) ---- *)
Definition alB_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x98 0xb0 0 0
    [YP09.mkChunk 0x98 (CVal 8 (SLit 0xfffffffc)); YP09.mkChunk 0xa0 (CVal 8 (SOff 35 0));
     YP09.mkChunk 0xa8 (CVal 8 (SLit 4097))].
Definition alB_ss (z : bool) : sstate := mkSS (kpc KP_PADN) k3_regs [alB_sp; k3_fl] None (a5B_facts z).

Lemma alB_windows : forall (E : env) z w,
  base_val E (Some 21%nat) = w ->
  forall b wlo whi a, In (b, wlo, whi) (windows (ss_mem (alB_ss z))) ->
    base_val E b + wlo <= a < base_val E b + whi -> w <= a < w + NW_SIZE.
Proof.
  intros E z w H21 b wlo whi a Hin Ha.
  unfold alB_ss, windows in Hin.
  cbn [ss_mem map In alB_sp k3_fl YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
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

(* ======================================== THE LATCH ======================================== *)

Lemma alL_start : forall (W3 : world SEGS) (ms3 : machine_state) l,
  kms KP_ALAT ms3 -> getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 22)) = w64 l ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) [])) (alL_ss l) (restrict (w_H W3) ms3).
Proof.
  intros W3 ms3 l (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs) R22.
  rewrite (kn_ms_shape ms3 (BASE + kpc KP_ALAT) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
  rewrite restrict_mkst_fx. unfold alL_ss. apply pa_entry_st_ok_full.
  - apply kn_regs_ok_set; [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
    rewrite R22. reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok alias_ok conds_ok]. exact (conj I (conj I I)).
Qed.

(* the cut after the latch: the same memory, the pc and the registers of the target *)
Lemma alL_end : forall cx fpos pc rl sl k2 ly3 S3 W3 (ms3 : machine_state) md3 adv j pc' rl' l (E : env)
    (ms : machine_state) md,
  kbase SK B cx ->
  kat B cx fpos pc rl sl (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  kslots_okb sl = true ->
  frame_of E (ss_mem (alL_ss l)) (mrestrict (w_H W3) (ms_mem ms3))
    (mrestrict (w_H W3) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  kms pc' ms -> kregs0 cx ms -> kregs_eq ms rl' ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  kat B cx fpos pc' rl' sl (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms md.
Proof.
  intros cx fpos pc rl sl k2 ly3 S3 W3 ms3 md3 adv j pc' rl' l E ms md HB HAT Hok HFr HG HMS HR0 HRL Hfds Hfs.
  apply (kat_frame_w2 SK B LAWS 0 0 cx fpos pc rl sl _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 pc' rl' sl
           W3 ms md HB HAT HMS HR0 HRL (fun x Hx => Hx) Hok (kfsh_fits _ _ _) Hfds Hfs ltac:(lia) ltac:(unfold NW_SIZE; lia)).
  - intros q Hq _.
    apply (kept_of_frame (segs := SEGS) _ _ (w_H W3) (ms_mem ms3) (ms_mem ms) (fun _ => False) HFr);
      [| exact Hq | intros []].
    intros b wlo whi x Hin. unfold alL_ss, windows in Hin. cbn [ss_mem map In] in Hin. destruct Hin.
  - intros q Hq. exact (k3_apres_grows _ _ _ q HG Hq).
Qed.

Theorem kn_alatch : forall POST (Rc Rm Ra Ra' : kcx -> Z -> Prop),
  (forall cx v, Ra cx v -> 2 <= v -> Ra' cx (v - 1)) ->
  kfrom SK B POST (kin_attr B Rc Rm Ra') -> kfrom SK B POST (kin_nlend B Rc Rm) ->
  kfrom SK B POST (kin_alat B Rc Rm Ra).
Proof.
  intros POST Rc Rm Ra Ra' HRA' HATT HNLE cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (c & ci & j & m & k & n & f & adv & hd & kd & l & HRc & HRm & HRa & Hc & Hci & Hj & Hm & Hk & Hkd
    & Hl & Hhd & HW & _ & HAT).
  pose proof HAT as (HMS & HR0 & HRL & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof (kn_reg_of ms3 _ 22 l HRL ltac:(kn_in)) as R22.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) []) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (SHOK : sh_ok SEGS k3_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  assert (Hok : kslots_okb (kslots_setup cx fpos c ++
                  [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)]) = true)
    by reflexivity.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
    (proj2 HAT))))))))) as (HF4 & HFc & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  (* the registers the latch keeps: s3, s5, s8, s9 *)
  assert (HKP : forall (msn : machine_state) ssx,
            st_ok_pi SEGS pa_val E ssx (restrict (w_H W3) msn) ->
            forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssx) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
              (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 25]%nat) = true ->
            forall r : nat, In r [19; 21; 24; 25]%nat ->
            getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))).
  { intros msn ssx HSx Hb r Hr. exact (regs_kept_of_st_ok_pi E ssx _ _ _ _ HSx HAG Hb _ (kn_in_map5 r _ Hr)). }
  (* w2 is kept: the run has no window *)
  assert (HKW : forall (msn : machine_state) l',
            frame_of E (ss_mem (alL_ss l')) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem msn)) ->
            mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem msn)) ->
            kw_at W3 msn (kW2 cx fpos) n f).
  { intros msn l' HFn HGn. apply (kn_kw_keep W3 ms3 msn (kW2 cx fpos) n f HW).
    - intros i Hi.
      apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem msn) (fun _ => False) HFn).
      + intros b wlo whi x Hin. unfold alL_ss, windows in Hin. cbn [ss_mem map In] in Hin. destruct Hin.
      + unfold kW2, KN_W2, NW_SIZE in *. lia.
      + intros [].
    - intros q Hq. exact (k3_apres_grows _ _ _ q HGn Hq). }
  destruct (Z.eq_dec l 1) as [L1 | L1].
  - (* the loop is done: nl_end *)
    subst l.
    pose proof (alL_start W3 ms3 1 HMS R22) as HS. rewrite <- HEdef in HS.
    paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_NLEND); [apply awr_ok_x_nil|].
    lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?mx) |- _ => rename mx into msn; rename HS' into HSn end.
    lazymatch goal with HF' : frame_of _ _ _ _ |- _ => rename HF' into HFn end.
    lazymatch goal with HG' : mem_grows _ _ |- _ => rename HG' into HGn end.
    apply (HNLE cx fpos k2 ly3 S3 W3 msn _ HB HJ HFR).
    exists c, ci, j, m, k, n, f, adv, hd, kd.
    split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
    split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|]. split; [exact Hhd|].
    split; [exact (HKW msn 1 HFn HGn)|].
    apply (alL_end cx fpos _ _ _ k2 ly3 S3 W3 ms3 md3 adv j KP_NLEND _ 1 E msn _ HB HAT Hok HFn HGn).
    + apply (kn_kms_of _ E _ msn KP_NLEND HSn); vm_compute; reflexivity.
    + exact (kregs0_keep cx ms3 msn
               (regs_kept_of_st_ok_pi E _ _ _ _ nx_keep0 HSn HAG ltac:(vm_compute; reflexivity)) HR0).
    + pose proof (HKP msn _ HSn ltac:(vm_compute; reflexivity)) as HKr.
      unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        lazymatch goal with |- getr (ms_regs _) (Z_to_bv 5 (Z.of_nat ?r)) = w64 _ =>
          rewrite <- (kn_reg_of _ _ r _ HRL ltac:(kn_in)); exact (HKr r ltac:(kn_in)) end.
    + exact (proj1 (wvb_fds_fs _ _ _)).
    + exact (proj2 (wvb_fds_fs _ _ _)).
  - (* one more attribute: left = 2, 3, 4 *)
    assert (Hl2 : 2 <= l) by lia.
    pose proof (HRA' cx l HRa Hl2) as HRa'.
    assert (Hl3 : l = 2 \/ l = 3 \/ l = 4) by lia.
    destruct Hl3 as [-> | [-> | ->]].
    all: pose proof (alL_start W3 ms3 _ HMS R22) as HS; rewrite <- HEdef in HS.
    all: paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_ATTR); [apply awr_ok_x_nil|].
    all: lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?mx) |- _ => rename mx into msn; rename HS' into HSn end.
    all: lazymatch goal with HF' : frame_of _ _ _ _ |- _ => rename HF' into HFn end.
    all: lazymatch goal with HG' : mem_grows _ _ |- _ => rename HG' into HGn end.
    all: apply (HATT cx fpos k2 ly3 S3 W3 msn _ HB HJ HFR).
    all: eexists c, ci, j, m, k, n, f, adv, hd, kd, _.
    all: split; [exact HRc|]; split; [exact HRm|]; split; [exact HRa'|]; split; [exact Hc|]; split; [exact Hci|].
    all: split; [exact Hj|]; split; [exact Hm|]; split; [exact Hk|]; split; [exact Hkd|]; split; [lia|].
    all: split; [exact Hhd|]; split; [exact (HKW msn _ HFn HGn)|]; split; [exact I|].
    all: apply (alL_end cx fpos _ _ _ k2 ly3 S3 W3 ms3 md3 adv j KP_ATTR _ _ E msn _ HB HAT Hok HFn HGn).
    all: try (apply (kn_kms_of _ E _ msn KP_ATTR HSn); vm_compute; reflexivity).
    all: try exact (kregs0_keep cx ms3 msn
               (regs_kept_of_st_ok_pi E _ _ _ _ nx_keep0 HSn HAG ltac:(vm_compute; reflexivity)) HR0).
    all: try exact (proj1 (wvb_fds_fs _ _ _)).
    all: try exact (proj2 (wvb_fds_fs _ _ _)).
    all: pose proof (HKP msn _ HSn ltac:(vm_compute; reflexivity)) as HKr.
    all: unfold kregs_eq; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: first [ lazymatch goal with |- getr (ms_regs _) (Z_to_bv 5 (Z.of_nat 22)) = _ =>
                   rewrite (st_ok_pi_restrict_reg _ E _ msn _ HSn); vm_compute; reflexivity end
               | lazymatch goal with |- getr (ms_regs _) (Z_to_bv 5 (Z.of_nat ?r)) = w64 _ =>
                   rewrite <- (kn_reg_of _ _ r _ HRL ltac:(kn_in)); exact (HKr r ltac:(kn_in)) end ].
Qed.

(* ======================================== nl_end ======================================== *)

(* the private cut at +0x1100 *)
Definition al_pad (Rc Rm : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv hd kd, Rc cx (c - ci) /\ Rm cx (m - k) /\
  1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= m <= 5 /\ 0 <= k < m /\ (kd = 0 \/ kd = 7) /\ 0 <= hd <= n /\
  kw_at W3 ms3 (kW2 cx fpos) n f /\
  kat B cx fpos KP_PADN [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, m)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

Definition al_ext (cx : kcx) (fpos n f k hd m : Z) : list word :=
  [w64 n; w64 f; w64 (kW2 cx fpos + n); w64 k; w64 hd; w64 (kW2 cx fpos + hd); w64 m].

Lemma al_env : forall cx fpos k2 ly3 S3 md3 (ms3 : machine_state) n f k hd m (E : env),
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kregs0 cx ms3 ->
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 21)) = w64 (kW2 cx fpos) ->
  0 <= n <= 4096 -> 0 <= f <= 1 -> 0 <= k < 5 -> 0 <= hd <= n -> 1 <= m <= 5 ->
  E = Eimg (Ereg (ms_regs ms3) (al_ext cx fpos n f k hd m)) ->
  bv_unsigned (ew E 9) = ksp1 cx /\ bv_unsigned (ew E 18) = ka0 cx /\ bv_unsigned (ew E 20) = SHADOW_OFF /\
  bv_unsigned (ew E 21) = kW2 cx fpos /\ bv_unsigned (ew E 32) = n /\ bv_unsigned (ew E 33) = f /\
  bv_unsigned (ew E 34) = kW2 cx fpos + n /\ bv_unsigned (ew E 35) = k /\ bv_unsigned (ew E 36) = hd /\
  bv_unsigned (ew E 37) = kW2 cx fpos + hd /\ bv_unsigned (ew E 38) = m.
Proof.
  intros cx fpos k2 ly3 S3 md3 ms3 n f k hd m E HB HJB HR0 R21 Hn Hf Hk Hhd Hm HEdef.
  destruct HR0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & _ & Hs1b & _ & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hka : 0 <= ka0 cx < 2 ^ 47)
    by (destruct (kn_ard_bound SK B LAWS cx (ka0 cx) HB (kn_ard_cur cx (ka0 cx) ltac:(lia))) as (Hq & _); lia).
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hj; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hj)).
  assert (EXT : forall jn, (jn < 7)%nat -> ew E (32 + jn) = nth jn (al_ext cx fpos n f k hd m) (Z_to_bv 64 0))
    by (intros jn Hj; rewrite HEdef, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
  pose proof (EXT 2%nat ltac:(lia)) as E34. pose proof (EXT 3%nat ltac:(lia)) as E35.
  pose proof (EXT 4%nat ltac:(lia)) as E36. pose proof (EXT 5%nat ltac:(lia)) as E37.
  pose proof (EXT 6%nat ltac:(lia)) as E38.
  cbn [al_ext nth Nat.add] in E32, E33, E34, E35, E36, E37, E38.
  assert (E9 : ew E 9 = w64 (ksp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact R9).
  assert (E18 : ew E 18 = w64 (ka0 cx)) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E20 : ew E 20 = w64 SHADOW_OFF) by (rewrite (ER 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = w64 (kW2 cx fpos))
    by (rewrite (ER 21%nat (Z_to_bv 5 (Z.of_nat 21)) eq_refl); exact R21).
  split; [rewrite E9; apply unsigned_lit_small; lia|].
  split; [rewrite E18; apply unsigned_lit_small; lia|].
  split; [rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia|].
  split; [rewrite E21; apply unsigned_lit_small; lia|].
  split; [rewrite E32; apply unsigned_lit_small; lia|].
  split; [rewrite E33; apply unsigned_lit_small; lia|].
  split; [rewrite E34; apply unsigned_lit_small; lia|].
  split; [rewrite E35; apply unsigned_lit_small; lia|].
  split; [rewrite E36; apply unsigned_lit_small; lia|].
  split; [rewrite E37; apply unsigned_lit_small; lia|].
  rewrite E38; apply unsigned_lit_small; lia.
Qed.

(* ---- (NA) THE START: the symbolic state, its shadow entries and its writable windows at +0x106c ---- *)
Lemma al_start : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 c ci j m k n f adv hd kd (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_NLEND
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  0 <= k < 5 -> 1 <= m <= 5 -> 0 <= hd <= n ->
  E = Eimg (Ereg (ms_regs ms3) (al_ext cx fpos n f k hd m)) ->
  forall nlo nhi (b37 b34 : bool) nt cs,
  nlo <= n <= nhi ->
  (if b37 then hd + 4 <= 4096 else True) ->
  (if b34 then n + 1 <= 4096 else True) ->
  (if b37 then (if b34 then hd + 4 <= n else True) else True) ->
  sv_denot E nt = Z_to_bv 64 (kW2 cx fpos + n) ->
  regions_wf (al_sp kd :: k3_fl :: al_ws b37 b34) = true ->
  conds_ok E cs ->
  st_ok_pi SEGS pa_val E (al_ss kd nlo nhi b37 b34 nt cs) (restrict (w_H W3) ms3) /\
  sh_ok SEGS k3_Bx (al_SH b37 b34) E (mrestrict (w_H W3) (ms_mem ms3)) /\
  awr_ok_x E (ss_mem (al_ss kd nlo nhi b37 b34 nt cs)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd E HB HJ HW HAT Hk Hm Hhd HEdef nlo nhi b37 b34 nt
    cs Hn H37 H34 H3734 Hnt Hwf Hcs.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  pose proof (kn_reg_of ms3 _ 25 (kW2 cx fpos + NW_N) HRL ltac:(kn_in)) as R25.
  pose proof HW as (Hw0 & Hwl & Hpres & Hnv & Hfv & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  destruct (al_env cx fpos k2 ly3 S3 md3 ms3 n f k hd m E HB HJB HR0 R21 ltac:(lia) Hfr Hk Hhd Hm HEdef)
    as (B9 & B18 & B20 & B21 & B32 & B33 & B34 & B35 & B36 & B37 & B38).
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
  assert (BV37 : base_val E (Some 37%nat) = kW2 cx fpos + hd) by exact B37.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M m HSL ltac:(apply in_or_app; right; kn_in)) as SL_M.
  pose proof (kn_slot_of cx W3 ms3 _ KS_KD kd HSL ltac:(apply in_or_app; right; kn_in)) as SL_KD.
  pose proof (kn_slot_of cx W3 ms3 _ KS_HD hd HSL ltac:(apply in_or_app; right; kn_in)) as SL_HD.
  pose proof (kn_slot_of cx W3 ms3 _ KS_MASK 0xfffffffc HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_MASK.
  pose proof (kn_slot_of cx W3 ms3 _ KS_K k HSL ltac:(apply in_or_app; right; kn_in)) as SL_K.
  pose proof (kn_slot_of cx W3 ms3 _ KS_ROOM 4097 HSL ltac:(apply in_or_app; right; kn_in)) as SL_ROOM.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W2F (kW2 cx fpos + NW_FULL) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_W2F.
  pose proof (a5_awf SK B LAWS cx fpos k2 ly3 S3 W3 _ _ HB HJ) as AWF.
  pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HRA.
  assert (HUB : U E k3_Bx = SHADOW_OFF)
    by (unfold k3_Bx; apply k3_U0; [exact B20 | unfold SHADOW_OFF; lia]).
  split; [|split].
  - (* the symbolic state *)
    rewrite (kn_ms_shape ms3 (BASE + kpc KP_NLEND) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold al_ss. apply pa_entry_st_ok_full.
    + unfold k3_regs.
      apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R25. cbn [sv_denot]. rewrite B21. reflexivity.
    + exact Hwf.
    + apply Forall_cons; [|apply Forall_cons].
      * unfold al_sp, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; [..|apply Forall_nil].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x68 (SOff 38 0) m); [|exact SL_M].
           cbn [sv_denot]. rewrite B38, Z.add_0_r. reflexivity.
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x88 (SLit kd) kd); [reflexivity | exact SL_KD].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x90 (SOff 36 0) hd); [|exact SL_HD].
           cbn [sv_denot]. rewrite B36, Z.add_0_r. reflexivity.
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x98 (SLit 0xfffffffc) 0xfffffffc);
             [reflexivity | exact SL_MASK].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xa0 (SOff 35 0) k); [|exact SL_K].
           cbn [sv_denot]. rewrite B35, Z.add_0_r. reflexivity.
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xa8 (SLit 4097) 4097);
             [reflexivity | exact SL_ROOM].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc8 (SOff 21 4104) (kW2 cx fpos + NW_FULL));
             [|exact SL_W2F].
           cbn [sv_denot]. rewrite B21. reflexivity.
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
      * destruct b37, b34; cbv iota in H37, H34, H3734; cbn [al_ws app];
          repeat apply Forall_cons; try apply Forall_nil;
          first [ unfold al_hr, region_ok;
                  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite BV37;
                  split; [lia|]; split; [unfold NW_SIZE in Hwl; lia|]; split; [|apply Forall_nil];
                  intros o Ho; replace (kW2 cx fpos + hd + o) with (kW2 cx fpos + (hd + o)) by lia;
                  exact (proj2 (Hpres (hd + o) ltac:(unfold NW_SIZE; lia)))
                | unfold al_nr, region_ok;
                  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite BV34;
                  split; [lia|]; split; [unfold NW_SIZE in Hwl; lia|]; split; [|apply Forall_nil];
                  intros o Ho; replace (kW2 cx fpos + n + o) with (kW2 cx fpos + (n + o)) by lia;
                  exact (proj2 (Hpres (n + o) ltac:(unfold NW_SIZE; lia))) ].
    + rewrite HKA in Hac.
      destruct b37, b34; cbv iota in H37, H34, H3734; cbn [al_ws app pairwise_disjoint all_disjoint];
        unfold extent_disjoint, al_sp, k3_fl, al_hr, al_nr;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?BV9, ?BV21, ?BV34, ?BV37;
        repeat split; lia.
    + unfold facts_ok. cbn [f_atoms f_conds f_alias al_atoms al_alias atoms_ok alias_ok].
      split; [|split].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B20, B21, B32, B33, B34, B36, B37.
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
        repeat split; lia.
      * exact Hcs.
      * split; [|split; [|exact I]].
        -- rewrite Hnt, (denot_lit_U E (SAlu ALU_ADD (SOff 21 0) (SOff 32 0))). f_equal.
           rewrite U_SAlu, !U_SOff. cbn [zalu_raw].
           rewrite B21, B32, !Z.add_0_r.
           rewrite (zcanon_id (kW2 cx fpos)), (zcanon_id n), zcanon_id by (unfold M64; lia). reflexivity.
        -- rewrite (denot_lit_U E (SAlu ALU_ADD (SOff 21 0) (SOff 36 0))), (denot_lit_U E (SOff 37 0)). f_equal.
           rewrite U_SAlu, !U_SOff. cbn [zalu_raw].
           rewrite B21, B36, B37, !Z.add_0_r.
           rewrite (zcanon_id (kW2 cx fpos)), (zcanon_id hd) by (unfold M64; lia). reflexivity.
  - (* the shadow entries *)
    unfold sh_ok, al_SH.
    apply Forall_cons.
    + apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E k3_Bx 21 (kW2 cx fpos) NW_SIZE (kW2 cx fpos)
               4096 4112 HRA HUB); [apply k3_U0; [exact B21 | lia] | lia | unfold NW_SIZE; lia |].
      intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
    + destruct b37, b34; cbn [app]; repeat apply Forall_cons; try apply Forall_nil;
        first [ apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E k3_Bx 37 (kW2 cx fpos) NW_SIZE
                         (kW2 cx fpos + hd) 0 11 HRA HUB); [apply k3_U0; [exact B37 | lia] | lia | unfold NW_SIZE; lia |];
                intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia; unfold SHADOW_OFF in *; lia
              | apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E k3_Bx 34 (kW2 cx fpos) NW_SIZE
                         (kW2 cx fpos + n) 0 8 HRA HUB); [apply k3_U0; [exact B34 | lia] | lia | unfold NW_SIZE; lia |];
                intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia; unfold SHADOW_OFF in *; lia ].
  - (* the writable windows lie in F *)
    unfold al_ss. cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; unfold al_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons.
    + intros x Hx. unfold k3_fl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV21 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
    + destruct b37, b34; cbn [al_ws app]; repeat apply awr_ok_x_cons; try apply awr_ok_x_nil;
        intros x Hx; cbn [al_hr al_nr YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite ?BV34, ?BV37 in Hx;
        left; apply AWF; unfold NW_SIZE; lia.
Qed.

(* ---- (NA) THE ENDS: the pad cut at +0x1100, and the cut after a message ---- *)
Lemma al_endP : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv hd kd (E : env),
  kfrom SK B POST (al_pad Rc Rm) ->
  kbase SK B cx ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) ->
  1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m -> (kd = 0 \/ kd = 7) -> 0 <= hd <= n ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_NLEND
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  bv_unsigned (ew E 21) = kW2 cx fpos -> bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 33) = f ->
  bv_unsigned (ew E 34) = kW2 cx fpos + n -> bv_unsigned (ew E 37) = kW2 cx fpos + hd ->
  bv_unsigned (ew E 38) = m ->
  forall nlo nhi b37 b34 nt cs, n + 1 <= 4112 -> hd + 4 <= 4112 ->
  forall (ms : machine_state) md cs',
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs') ->
  frame_of E (ss_mem (al_ss kd nlo nhi b37 b34 nt cs)) (mrestrict (w_H W3) (ms_mem ms3))
    (mrestrict (w_H W3) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  kms KP_PADN ms ->
  (forall r, In r nx_keep0 -> getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  (forall r, In r (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24]%nat) ->
     getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 25)) = sv_denot E (SOff 21 4096) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 22)) = sv_denot E (SOff 38 0) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  In (YP09.mkChunk 4096 (CVal 8 (SOff 32 0))) cs' ->
  In (YP09.mkChunk 4104 (CVal 4 (SOff 33 0))) cs' ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd E HN HB HFR HRc HRm Hc Hci Hj Hm Hk Hkd
    Hhd HW HAT B21 B32 B33 B34 B37 B38 nlo nhi b37 b34 nt cs Hn1 Hh4 ms md cs' HR1 HFr HG HJ HMS HK0 HKN H25 H22 Hfds
    Hfs Hin1 Hin2.
  pose proof HAT as (_ & HR0 & HRL & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV34 : base_val E (Some 34%nat) = kW2 cx fpos + n) by exact B34.
  assert (BV37 : base_val E (Some 37%nat) = kW2 cx fpos + hd) by exact B37.
  assert (HP : forall q, apresent (w_H W3) (ms_mem ms3) q -> apresent (w_H W3) (ms_mem ms) q)
    by (intros q Hq; exact (k3_apres_grows _ _ _ q HG Hq)).
  assert (HK : forall r : nat, In r [21; 24]%nat ->
            getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
    by (intros r Hr; exact (HKN _ (kn_in_map5 r _ Hr))).
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  exists c, ci, j, m, k, n, f, adv, hd, kd.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|]. split; [exact Hhd|].
  split.
  { apply (kw_move W3 ms3 W3 ms (kW2 cx fpos) n f n f HW HP).
    - exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4096 8 (SOff 32 0) n HR1 B21 Hin1
               ltac:(cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
    - exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SOff 33 0) f HR1 B21 Hin2
               ltac:(cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
    - unfold NL_CHUNK_MAX. lia.
    - exact Hfr. }
  apply (kat_frame_w2 SK B LAWS 0 NW_SIZE cx fpos KP_NLEND _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 KP_PADN _ _
           W3 ms md HB HAT HMS (kregs0_keep cx ms3 ms HK0 HR0)).
  - unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    + rewrite (HK 21%nat) by kn_in. apply (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL). kn_in.
    + rewrite (HK 24%nat) by kn_in. apply (kn_reg_of ms3 _ 24 (kS8 cx) HRL). kn_in.
    + rewrite H25. cbn [sv_denot]. rewrite B21. reflexivity.
    + rewrite H22. cbn [sv_denot]. rewrite B38, Z.add_0_r. reflexivity.
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
    exact (al_windows E kd nlo nhi b37 b34 nt cs (kW2 cx fpos) n hd BV21 BV34 BV37 ltac:(lia) Hn1 ltac:(lia) Hh4).
  - exact HP.
Qed.

Lemma al_endN : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv hd kd (E : env),
  kfrom SK B POST (kin_next B Rc Rm) ->
  kbase SK B cx ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) ->
  1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m -> 0 <= hd <= n ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_NLEND
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  bv_unsigned (ew E 21) = kW2 cx fpos -> bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 33) = f ->
  bv_unsigned (ew E 34) = kW2 cx fpos + n -> bv_unsigned (ew E 35) = k -> bv_unsigned (ew E 37) = kW2 cx fpos + hd ->
  bv_unsigned (ew E 38) = m ->
  forall nlo nhi b37 b34 nt cs, n + 1 <= 4112 -> hd + 4 <= 4112 ->
  forall pl, 0 <= pl -> n + pl <= 4096 ->
  forall (ms : machine_state) md cs' fe f',
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs') ->
  frame_of E (ss_mem (al_ss kd nlo nhi b37 b34 nt cs)) (mrestrict (w_H W3) (ms_mem ms3))
    (mrestrict (w_H W3) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  kms KP_NEXT ms ->
  (forall r, In r nx_keep0 -> getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  (forall r, In r (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24]%nat) ->
     getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 25)) = sv_denot E (SOff 21 4096) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 22)) = sv_denot E (SOff 38 0) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 14)) = sv_denot E (SOff 35 0) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  In (YP09.mkChunk 4096 (CVal 8 (SOff 32 pl))) cs' ->
  In (YP09.mkChunk 4104 (CVal 4 fe)) cs' ->
  (fe = SOff 33 0 /\ f' = f) \/ (fe = SLit 1 /\ f' = 1) ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd E HN HB HFR HRc HRm Hc Hci Hj Hm Hk Hhd
    HW HAT B21 B32 B33 B34 B35 B37 B38 nlo nhi b37 b34 nt cs Hn1 Hh4 pl Hpl Hnpl ms md cs' fe f' HR1 HFr HG HJ HMS
    HK0 HKN H25 H22 H14 Hfds Hfs Hin1 Hin2 Hfe.
  pose proof HAT as (_ & HR0 & HRL & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV34 : base_val E (Some 34%nat) = kW2 cx fpos + n) by exact B34.
  assert (BV37 : base_val E (Some 37%nat) = kW2 cx fpos + hd) by exact B37.
  assert (Hf' : 0 <= f' <= 1) by (destruct Hfe as [(_ & ->) | (_ & ->)]; lia).
  assert (HP : forall q, apresent (w_H W3) (ms_mem ms3) q -> apresent (w_H W3) (ms_mem ms) q)
    by (intros q Hq; exact (k3_apres_grows _ _ _ q HG Hq)).
  assert (HK : forall r : nat, In r [21; 24]%nat ->
            getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
    by (intros r Hr; exact (HKN _ (kn_in_map5 r _ Hr))).
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  exists c, ci, j, m, k, (n + pl), f', adv.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hm|]. split; [exact Hk|].
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
  apply (kat_frame_w2 SK B LAWS 0 NW_SIZE cx fpos KP_NLEND _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 KP_NEXT _ _
           W3 ms md HB HAT HMS (kregs0_keep cx ms3 ms HK0 HR0)).
  - unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    + rewrite (HK 21%nat) by kn_in. apply (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL). kn_in.
    + rewrite (HK 24%nat) by kn_in. apply (kn_reg_of ms3 _ 24 (kS8 cx) HRL). kn_in.
    + rewrite H25. cbn [sv_denot]. rewrite B21. reflexivity.
    + rewrite H14. cbn [sv_denot]. rewrite B35, Z.add_0_r. reflexivity.
    + rewrite H22. cbn [sv_denot]. rewrite B38, Z.add_0_r. reflexivity.
  - intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact Hx|].
    right. cbn [In] in Hx |- *. tauto.
  - reflexivity.
  - apply kfsh_fits.
  - exact Hfds.
  - exact Hfs.
  - lia.
  - lia.
  - intros q Hq Hnq.
    apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms)
             (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr); [|exact Hq | intros Hc'; apply Hnq; lia].
    exact (al_windows E kd nlo nhi b37 b34 nt cs (kW2 cx fpos) n hd BV21 BV34 BV37 ltac:(lia) Hn1 ltac:(lia) Hh4).
  - exact HP.
Qed.

(* ---- (NA) the run of one arm (KST: al_start at the cut; KP / KN: al_endP / al_endN at the cut) ---- *)
Ltac al_goP KST KP RUNTO HJ HAG B32 B34 B36 B37 kd nlo nhi b37 b34 nt cs :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAWR := fresh "HAWR" in
  destruct (KST nlo nhi b37 b34 nt cs ltac:(lia) ltac:(cbv iota; first [exact I | lia])
              ltac:(cbv iota; first [exact I | lia]) ltac:(cbv iota; first [exact I | lia])
              ltac:(first [cbn [sv_denot]; rewrite B34, Z.add_0_r; reflexivity
                          | cbn [sv_denot]; rewrite B37; f_equal; lia])
              ltac:(vm_compute; reflexivity) ltac:(al_conds B32 B36)) as (HS & SHOK & HAWR);
  paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_PADN); [exact HAWR|];
  lazymatch goal with
  | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
    HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
    HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    let HR1 := fresh "HR1" in
    spregion HS' 1%nat HR1;
    apply (KP nlo nhi b37 b34 nt cs ltac:(lia) ltac:(lia) msn mdn _ HR1 HFr' HG');
    [ assumption
    | apply (kn_kms_of _ E ssx msn KP_PADN HS'); vm_compute; reflexivity
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24]%nat)
               HS' HAG ltac:(vm_compute; reflexivity))
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | exact (proj1 (wvb_fds_fs _ _ _))
    | exact (proj2 (wvb_fds_fs _ _ _))
    | kn_in
    | kn_in ]
  end.

Ltac al_goN KST KN RUNTO HJ HAG B32 B34 B36 B37 kd nlo nhi b37 b34 nt cs pl fv fe :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAWR := fresh "HAWR" in
  destruct (KST nlo nhi b37 b34 nt cs ltac:(lia) ltac:(cbv iota; first [exact I | lia])
              ltac:(cbv iota; first [exact I | lia]) ltac:(cbv iota; first [exact I | lia])
              ltac:(first [cbn [sv_denot]; rewrite B34, Z.add_0_r; reflexivity
                          | cbn [sv_denot]; rewrite B37; f_equal; lia])
              ltac:(vm_compute; reflexivity) ltac:(al_conds B32 B36)) as (HS & SHOK & HAWR);
  paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_NEXT); [exact HAWR|];
  lazymatch goal with
  | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
    HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
    HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    let HR1 := fresh "HR1" in
    spregion HS' 1%nat HR1;
    apply (KN nlo nhi b37 b34 nt cs ltac:(lia) ltac:(lia) pl ltac:(lia) ltac:(lia) msn mdn _ fe fv HR1 HFr' HG');
    [ assumption
    | apply (kn_kms_of _ E ssx msn KP_NEXT HS'); vm_compute; reflexivity
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24]%nat)
               HS' HAG ltac:(vm_compute; reflexivity))
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | exact (proj1 (wvb_fds_fs _ _ _))
    | exact (proj2 (wvb_fds_fs _ _ _))
    | kn_in
    | kn_in
    | first [left; split; reflexivity | right; split; reflexivity] ]
  end.

(* ---- (NA) THE PHASE: nl_end to the pad or to the cut after a message ---- *)
Theorem al_nla : forall POST (Rc Rm : kcx -> Z -> Prop),
  kfrom SK B POST (al_pad Rc Rm) -> kfrom SK B POST (kin_next B Rc Rm) -> kfrom SK B POST (kin_nlend B Rc Rm).
Proof.
  intros POST Rc Rm HPD HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qc & qci & qj & qm & qk & qn & qf & qadv & qhd & qkd & HRc & HRm & Hc & Hci & Hj & Hm & Hk & Hkd
    & Hhd & HW & HAT).
  pose proof HAT as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  remember (Eimg (Ereg (ms_regs ms3) (al_ext cx fpos qn qf qk qhd qm))) as Eq3 eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM Eq3) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (al_ext cx fpos qn qf qk qhd qm)) Eq3)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (al_env cx fpos k2 ly3 S3 md3 ms3 qn qf qk qhd qm Eq3 HB HJB HR0 R21 ltac:(lia) Hfr ltac:(lia) Hhd Hm
              HEdef) as (B9 & B18 & B20 & B21 & B32 & B33 & B34' & B35 & B36 & B37' & B38).
  pose proof (al_start cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd Eq3 HB HJ HW HAT
                ltac:(lia) Hm Hhd HEdef) as KST.
  pose proof (al_endP POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd Eq3 HPD HB HFR HRc
                HRm Hc Hci Hj Hm Hk Hkd Hhd HW HAT B21 B32 B33 B34' B37' B38) as KP.
  pose proof (al_endN POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd Eq3 HN HB HFR HRc
                HRm Hc Hci Hj Hm Hk Hhd HW HAT B21 B32 B33 B34' B35 B37' B38) as KN.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  destruct Hkd as [Hk0 | Hk7]; subst qkd.
  - (* kind 0: the pad *)
    destruct (Z_lt_ge_dec qn (qhd + 4)) as [A|A].
    + al_goP KST KP RUNTO HJ HAG B32 B34' B36 B37' 0 0 4096 false false (SOff 34 0) [al_lt 0].
    + al_goP KST KP RUNTO HJ HAG B32 B34' B36 B37' 0 0 4096 true false (SOff 34 0) [al_ge 0].
  - (* kind 7 *)
    destruct (Z.eq_dec (qn mod 4) 0) as [Hal|Hal].
    + destruct (Z_lt_ge_dec qn 4096) as [Hlt|Hge].
      * destruct (Z_lt_ge_dec qn (qhd + 4)) as [A|A].
        -- destruct (Z_lt_ge_dec (qn + 1) (qhd + 4)) as [C|C].
           ++ al_goN KST KN RUNTO HJ HAG B32 B34' B36 B37' 7 0 4095 false true (SOff 34 0) [al_lt 0; al_eq; al_srl; al_lt 1]
                1 qf (SOff 33 0).
           ++ al_goN KST KN RUNTO HJ HAG B32 B34' B36 B37' 7 0 4095 true false (SOff 37 3) [al_lt 0; al_eq; al_srl; al_ge 1]
                1 qf (SOff 33 0).
        -- al_goN KST KN RUNTO HJ HAG B32 B34' B36 B37' 7 0 4095 true true (SOff 34 0) [al_ge 0; al_eq; al_srl; al_ge 1]
             1 qf (SOff 33 0).
      * destruct (Z_lt_ge_dec qn (qhd + 4)) as [A|A].
        -- al_goN KST KN RUNTO HJ HAG B32 B34' B36 B37' 7 4096 4096 false false (SOff 34 0) [al_lt 0; al_eq] 0 1 (SLit 1).
        -- al_goN KST KN RUNTO HJ HAG B32 B34' B36 B37' 7 4096 4096 true false (SOff 34 0) [al_ge 0; al_eq] 0 1 (SLit 1).
    + destruct (Z_lt_ge_dec qn (qhd + 4)) as [A|A].
      * al_goP KST KP RUNTO HJ HAG B32 B34' B36 B37' 7 0 4096 false false (SOff 34 0) [al_lt 0; al_ne].
      * al_goP KST KP RUNTO HJ HAG B32 B34' B36 B37' 7 0 4096 true false (SOff 34 0) [al_ge 0; al_ne].
Qed.

(* ======================================== (NB) the pad ======================================== *)

Lemma alB_start : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 c ci j m k n f adv hd kd (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_PADN [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, m)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  0 <= k < 5 ->
  E = Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos n f k)) ->
  forall z : bool, (if z then n mod 4 = 0 else n mod 4 <> 0) ->
  st_ok_pi SEGS pa_val E (alB_ss z) (restrict (w_H W3) ms3) /\
  awr_ok_x E (ss_mem (alB_ss z)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd E HB HJ HW HAT Hk HEdef z Hz.
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
  pose proof (kn_slot_of cx W3 ms3 _ KS_K k HSL ltac:(apply in_or_app; right; kn_in)) as SL_K.
  pose proof (kn_slot_of cx W3 ms3 _ KS_ROOM 4097 HSL ltac:(apply in_or_app; right; kn_in)) as SL_ROOM.
  pose proof (a5_awf SK B LAWS cx fpos k2 ly3 S3 W3 _ _ HB HJ) as AWF.
  split.
  - (* the symbolic state *)
    rewrite (kn_ms_shape ms3 (BASE + kpc KP_PADN) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold alB_ss. apply pa_entry_st_ok_full.
    + unfold k3_regs.
      apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R25. cbn [sv_denot]. rewrite B21. reflexivity.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold alB_sp, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; [..|apply Forall_nil].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x98 (SLit 0xfffffffc) 0xfffffffc);
             [reflexivity | exact SL_MASK].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xa0 (SOff 35 0) k); [|exact SL_K].
           cbn [sv_denot]. rewrite B35, Z.add_0_r. reflexivity.
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xa8 (SLit 4097) 4097);
             [reflexivity | exact SL_ROOM].
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
    + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, alB_sp, k3_fl.
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
    unfold alB_ss. cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; unfold alB_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold k3_fl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV21 in Hx.
    left. apply AWF. unfold NW_SIZE. lia.
Qed.

Lemma alB_end : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv hd kd,
  kfrom SK B POST (kin_next B Rc Rm) ->
  kbase SK B cx ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) ->
  1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_PADN [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, m)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  forall (E : env) (ms : machine_state) md cs',
  bv_unsigned (ew E 21) = kW2 cx fpos -> bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 33) = f ->
  bv_unsigned (ew E 35) = k ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= a < ksp1 cx)) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms) a) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  kms KP_NEXT ms ->
  (forall r, In r nx_keep0 -> getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  (forall r, In r (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24; 22]%nat) ->
     getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 25)) = sv_denot E (SOff 21 4096) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 14)) = sv_denot E (SOff 35 0) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  In (YP09.mkChunk 4096
        (CVal 8 (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SUB (SAlu ALU_AND (SOff 32 3) (SLit 0xfffffffc)) (SOff 32 0)))))
     cs' ->
  In (YP09.mkChunk 4104 (CVal 4 (SOff 33 0))) cs' ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd HN HB HFR HRc HRm Hc Hci Hj Hm Hk HW HAT
    E ms md cs' B21 B32 B33 B35 HR1 UN HP HJ HMS HK0 HKN H25 H14 Hfds Hfs Hin1 Hin2.
  pose proof HAT as (_ & HR0 & HRL & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HK : forall r : nat, In r [21; 24; 22]%nat ->
            getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
    by (intros r Hr; exact (HKN _ (kn_in_map5 r _ Hr))).
  assert (Hn' : U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SUB (SAlu ALU_AND (SOff 32 3) (SLit 0xfffffffc)) (SOff 32 0)))
                = (n + 0 + 3) / 4 * 4) by exact (a5_U_fin E n 0 3 B32 eq_refl ltac:(lia)).
  rewrite Z.add_0_r in Hn'.
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  exists c, ci, j, m, k, ((n + 3) / 4 * 4), f, adv.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hm|]. split; [exact Hk|].
  split.
  { apply (kw_move W3 ms3 W3 ms (kW2 cx fpos) n f ((n + 3) / 4 * 4) f HW HP).
    - refine (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4096 8 _ ((n + 3) / 4 * 4) HR1 B21 Hin1 _
               ltac:(cbn; lia) ltac:(cbn; lia)).
      rewrite denot_lit_U, Hn'. reflexivity.
    - exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SOff 33 0) f HR1 B21 Hin2
               ltac:(cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
    - unfold NL_CHUNK_MAX. lia.
    - exact Hfr. }
  apply (kat_frame_w2s SK B LAWS 0 NW_SIZE cx fpos KP_PADN _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 KP_NEXT _ _
           W3 ms md HB HAT HMS (kregs0_keep cx ms3 ms HK0 HR0)).
  - unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    + rewrite (HK 21%nat) by kn_in. apply (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL). kn_in.
    + rewrite (HK 24%nat) by kn_in. apply (kn_reg_of ms3 _ 24 (kS8 cx) HRL). kn_in.
    + rewrite H25. cbn [sv_denot]. rewrite B21. reflexivity.
    + rewrite H14. cbn [sv_denot]. rewrite B35, Z.add_0_r. reflexivity.
    + rewrite (HK 22%nat) by kn_in. apply (kn_reg_of ms3 _ 22 m HRL). kn_in.
  - intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact Hx|].
    right. cbn [In] in Hx |- *. tauto.
  - reflexivity.
  - apply kfsh_fits.
  - exact Hfds.
  - exact Hfs.
  - lia.
  - lia.
  - intros q Hq Hnq. apply UN; [exact Hq|]. intros [Hc'|Hc']; apply Hnq; [left; lia | right; exact Hc'].
  - exact HP.
Qed.

(* the models: a run materializes the lazy backing; a call keeps descriptors and files *)
Ltac a5_md := first [ exact (proj1 (wvb_fds_fs _ _ _)) | exact (proj2 (wvb_fds_fs _ _ _)) | reflexivity ].

(* ---- (NB) THE PHASE: nl_pad of kinds 0, 7 ---- *)
Theorem al_padl : forall POST (Rc Rm : kcx -> Z -> Prop),
  kfrom SK B POST (kin_next B Rc Rm) -> kfrom SK B POST (al_pad Rc Rm).
Proof.
  intros POST Rc Rm HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qc & qci & qj & qm & qk & qn & qf & qadv & qhd & qkd & HRc & HRm & Hc & Hci & Hj & Hm & Hk & Hkd
    & Hhd & HW & HAT).
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
  assert (BV21 : base_val Eq3 (Some 21%nat) = kW2 cx fpos) by exact B21.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof (kn_sp SK B cx HB) as (Hac & Hsp2 & _ & Hs1 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & Hs1c & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  pose proof (alB_start cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd Eq3 HB HJ HW HAT
                ltac:(lia) HEdef) as KST.
  pose proof (alB_end POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd HN HB HFR HRc
                HRm Hc Hci Hj Hm Hk HW HAT) as KFIN.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose proof (a5_shok_fl SK B LAWS cx fpos k2 ly3 S3 md3 W3 (ms_mem ms3) Eq3 HB HJB
                (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) B20 B21) as SHOK.
  destruct (Z.eq_dec (qn mod 4) 0) as [Hz|Hz].
  - (* n a multiple of 4: one run *)
    destruct (KST true Hz) as (HS & HAWR).
    paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_NEXT); [exact HAWR|].
    lazymatch goal with
    | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
      HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      let HR1 := fresh "HR1" in
      spregion HS' 1%nat HR1;
      apply (KFIN E msn mdn _ B21 B32 B33 B35 HR1);
      [ intros q Hq Hnq;
        apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem msn)
                 (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr');
        [exact (alB_windows E true (kW2 cx fpos) BV21) | exact Hq | intros Hc'; apply Hnq; left; exact Hc']
      | intros q Hq; exact (k3_apres_grows _ _ _ q HG' Hq)
      | assumption
      | apply (kn_kms_of _ E ssx msn KP_NEXT HS'); vm_compute; reflexivity
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
  - (* else: a run to the call, checked_memset(w2 + n, 0, pad), a run to the cut after a message *)
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
        [exact (alB_windows Eq3 false (kW2 cx fpos) BV21) | exact Hq | exact Hnq]. }
    pose proof (fun q Hq => k3_apres_grows _ _ _ q HG1 Hq) as P1.
    pose proof (a5_reg_same Eq3 _ _ (w_H W3) ms3 ms1 [2; 3; 4] HS0 HS1 ltac:(vm_compute; reflexivity)) as KEEP.
    sreg HS1 (10%bv : bv 5) R10. sreg HS1 (11%bv : bv 5) R11. sreg HS1 (12%bv : bv 5) R12.
    prreg HS1 (1%bv : bv 5) R1.
    cbn [ms_regs restrict mkst] in R10, R11, R12.
    pmkst HS1.
    rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memset) with 0x53214.
    eapply (a5_call_ms SK B LAWS AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 (ms_mem ms1) _ (ms_regs ms1) _ qn
              ((qn + 3) / 4 * 4 - qn) (POST cx) HB HJ HJB HSH UN1);
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
    assert (C35 : bv_unsigned (ew E2 35) = qk) by (rewrite HE2, ew_havoc_old by lia; exact B35).
    assert (C20 : bv_unsigned (ew E2 20) = SHADOW_OFF) by (rewrite HE2, ew_havoc_old by lia; exact B20).
    assert (CV21 : base_val E2 (Some 21%nat) = kW2 cx fpos) by exact C21.
    clear HE2.
    assert (UNc : forall q, 0 <= q < 2 ^ 64 ->
              ~ ((kW2 cx fpos <= q < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= q < ksp1 cx)) ->
              aview SEGS (w_H W3) mem2 q = aview SEGS (w_H W3) (ms_mem ms3) q).
    { intros q Hq Hnq.
      rewrite (Hfr2 q Hq ltac:(intros Hc'; apply Hnq; left; unfold NW_SIZE; lia)
                 ltac:(intros Hc'; apply Hnq; right; exact Hc')).
      apply UN1; [exact Hq | intros Hc'; apply Hnq; left; exact Hc']. }
    pose proof (a5_shok_fl SK B LAWS cx fpos k2 ly3 S3 md3 W3 mem2 E2 HB HJB
                  (a5_w2_ra SK B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 mem2 HB HJB HSH UNc) C20 C21) as SHOK2.
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 k3_span (kpc KP_NEXT).
    { cbn [ss_mem].
      apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
      apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite CV21 in Hx.
      left. apply (a5_awf SK B LAWS cx fpos k2 ly3 S3 W3 _ _ HB HJ2). unfold NW_SIZE. lia. }
    lazymatch goal with
    | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
      HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      let HR1 := fresh "HR1" in
      spregion HS' 1%nat HR1;
      apply (KFIN E msn mdn _ C21 C32 C33 C35 HR1);
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
      | apply (kn_kms_of _ E ssx msn KP_NEXT HS'); vm_compute; reflexivity
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
Theorem kn_nlend : forall POST (Rc Rm : kcx -> Z -> Prop),
  kfrom SK B POST (kin_next B Rc Rm) -> kfrom SK B POST (kin_nlend B Rc Rm).
Proof. intros POST Rc Rm HN. exact (al_nla POST Rc Rm (al_padl POST Rc Rm HN) HN). Qed.

End b.
End a.

Print Assumptions kn_alatch.
Print Assumptions kn_nlend.
