(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module paths and module names changed; 1077 of its 1137 lines of code are new or changed and 1245 lines of the source are left out. *)
(* model_decide (image A 0x8855c, listing offset AF_model_decide = 0x6390) and reac_served_decide (0x89510,
   AF_reac_served_decide = 0x7344) on image A (fuzz_link.asan, the PUBLISHED pin): the walks of both entries against
   their contracts lib/A/Prog/model_decide_c.v, `decide_acontract_at pc prefix vlan` (link_amem.v's aleaf_rd shape,
   K = DECIDE_AK = 8208, EV = 0, SIDE = [], the empty write set, the read set decide_ard):

     model_decide_aproof       : model_decide_acontract SK pa_segs PCAP_RLO PCAP_RHI B
     reac_served_decide_aproof : reac_served_decide_acontract SK pa_segs PCAP_RLO PCAP_RHI B

   at the relro constants of lib/A/Prog/PcapRelro.v; both are instances of decide_walk_md / decide_walk_rsd, which
   hold at every rlo rhi (the walk reads only the in-segment half of arodata_okP, for the wrappers' rt_rom_view).
   SK is any sink head (the tops are generic in it).

   Both are the one statement decide_acontract_at at the two entries and their two literal pairs. The two listings
   hold the same words but for the pc-relative ones (LinkList.v resolves them: PHi / PLdHi / PAddHi with the objects
   A_OBJ 32 / A_OBJ 33 for model_decide's "reac-pw:" 0x21160 and "vlan" 0x211c0, A_OBJ 43 / A_OBJ 44 for
   reac_served_decide's 0x212a0 and 0x212c0), so one script (dec_setup, dec_run, dec_branch, dec_null, dec_alias,
   dec_reshape, dec_empty, dec_prefix) walks both: it reads every entry-specific number (the entry, the return slots,
   the objects) off the symbolic states, and each Qed checks it at its entry.

   The walk runs the listing symbolically inside the caller's journal `ajournal_gx` (LinkWalk.v's paj_run_x, LinkPaLib's
   paj_run_tok / psrr_branch_tok / paj_ret_at) and ends with LinkWalk.v's apost_leaf. Which instruction needs which
   premise, beyond the contract header:
   - +0x00 / +0x04 (the frame push and the store of ra): the journal's window holds [sp - 16, sp) (apre's
     sp0 - STK <= sp - K, sp <= sp0); the store is an awr_byte of the journal's own window.
   - +0x08 beqz a1: decided by the Pre's astr_arg on a1 (NULL <-> no alias string).
   - +0x0c .. +0x14 (the shadow base through the .got cell): AR's const law (al_const) with PALib's pal_got_shadow /
     pal_cell (objects A_OBJ 1 and A_OBJ 64); the base is the atom 32 pinned to SHADOW_OFF.
   - +0x18 .. +0x24 (the instrumented check of alias[0]): the runner's token rule with the shadow entry
     [mkSHE 11 0 1] (dec_shok), whose sh_ok is the Pre's astr_rt_ok (range_addressable over alias's |t| + 1 bytes,
     and amem_range for the band); the token rule covers both arms of the shadow byte, and the error path
     errpath_load1 (0x5a31c) is not reached.
   - +0x28 lbu alias[0]: the region of alias's first byte (alias_region, the atom 33 holding the byte), added after
     the two read-only .got regions are dropped (the alias string may lie anywhere in the image, so it is not apart
     from them); it is apart from the frame by astr_rt_ok's apart_frame.
   - +0x44 / +0x60 (the two wrapper calls, at sp - 16, window 2 * ESTACK): the journal (aj_gx_ecall_pre), the Pre's
     acstr_at / astr_rt_ok of both strings, arodata_okP for the read-only image view the wrappers ask for; the
     strings and their shadow are outside [sp - K, sp), so the frame store and the walk keep them.
   - +0x84 ret: ret_ok of ra; the callee-saved registers from the symbolic state (aregs_preserved_of_st_ok).

   Section hypotheses (each a callee contract proved elsewhere, or the image instance):
   - STRNCMP : RtString.astrncmp_realizes pa_segs B (pa_sigma LS___interceptor_trampoline_strncmp), discharged at
     link's instance by lib/A/Rt/RtClosed.v `cmd_strncmp_closed : RtString.astrncmp_realizes tfibsegs B 0x43050`.
   - STRCMP : RtString.astrcmp_realizes pa_segs B (pa_sigma LS___interceptor_trampoline_strcmp), discharged at
     link's instance by lib/A/Rt/RtStrcmpClosed.v `link_strcmp_closed : RtString.astrcmp_realizes tfibsegs B 0x4304c`.
   - LAWS : AR_laws pa_segs B, TL : PALib B, HV : LinkVals (LinkWalk.v): the image instance, as every walk takes it.
   The two wrapper calls are LinkWalk.v's aj_gx_strncmp_sm_at and aj_gx_strcmp_at (the journal lifts that keep
   `same_but_materialized mdc md2`, which apost needs for the descriptors and the file system), applied by
   `dec_strncmp_call` / `dec_strcmp_call` with the string premises derived from the Pre.
   Released proofs (rule 24): none of model_decide or reac_served_decide
   (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).
   Proves model_decide and reac_served_decide (kind: function walk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c PcapRelro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The two wrapper answers, as link_spec.v's `decide` reads them
   ========================================================================== *)

Lemma dec_walk_prefix : forall (r : list byte) n (s : list byte),
  length r = S n -> ~ In (Z_to_bv 8 0) r -> ~ In (Z_to_bv 8 0) s ->
  (StrFun.strncmp_walk (s ++ [Z_to_bv 8 0]) (r ++ [Z_to_bv 8 0]) n = Some 0 <-> firstn (S n) s = r).
Proof.
induction r as [|b r IH]; intros n s Hlen Hr Hs; [cbn in Hlen; lia|].
assert (Hb : bv_unsigned b <> 0).
{ intros H0. apply Hr. left. apply bv_eq. rewrite H0. reflexivity. }
destruct s as [|a s].
- cbn [app StrFun.strncmp_walk].
  change (bv_unsigned (Z_to_bv 8 0)) with 0. cbn [Z.eqb orb].
  split; intros H; [injection H as H; lia | discriminate H].
- assert (Ha : bv_unsigned a <> 0).
  { intros H0. apply Hs. left. apply bv_eq. rewrite H0. reflexivity. }
  cbn [app StrFun.strncmp_walk].
  rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hb). cbn [orb].
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Hab|Hab].
  + assert (a = b) as <- by (apply bv_eq; exact Hab). cbn [negb].
    destruct n as [|n].
    * cbn [Nat.eqb orb]. cbn in Hlen. destruct r as [|x r]; [|cbn in Hlen; lia].
      cbn [firstn]. split; intros _; [reflexivity | f_equal; lia].
    * cbn [Nat.eqb orb]. cbn in Hlen.
      pose proof (IH n s ltac:(lia) ltac:(intros H; apply Hr; right; exact H) ltac:(intros H; apply Hs; right; exact H)) as IHn.
      cbn [firstn]. split; intros H; [apply IHn in H; rewrite H; reflexivity | injection H as H; apply IHn; exact H].
  + cbn [negb]. rewrite Bool.orb_true_r.
    split; intros H; [injection H as H; lia | cbn [firstn] in H; injection H as H _; subst b; lia].
Qed.

Lemma S_PREFIX_nz : ~ In (Z_to_bv 8 0) S_PREFIX.
Proof.
unfold S_PREFIX. cbn [map In]. intros H.
repeat (destruct H as [H|H]; [apply (f_equal (fun x : bv 8 => bv_unsigned x)) in H; vm_compute in H; discriminate H|]).
exact H.
Qed.

(* strncmp(alias, "reac-pw:", 8) == 0 is `has_prefix alias` *)
Lemma strncmp_prefix_iff : forall s, ~ In (Z_to_bv 8 0) s ->
  (StrFun.strncmp_model (s ++ [Z_to_bv 8 0]) (S_PREFIX ++ [Z_to_bv 8 0]) 8 = Some 0 <-> has_prefix s = true).
Proof.
intros s Hs.
change (StrFun.strncmp_model (s ++ [Z_to_bv 8 0]) (S_PREFIX ++ [Z_to_bv 8 0]) 8)
  with (StrFun.strncmp_walk (s ++ [Z_to_bv 8 0]) (S_PREFIX ++ [Z_to_bv 8 0]) 7).
pose proof (dec_walk_prefix S_PREFIX 7 s eq_refl S_PREFIX_nz Hs) as H1.
pose proof (bl_eqb_iff (firstn 8 s) S_PREFIX) as H2.
unfold has_prefix. tauto.
Qed.

(* ==========================================================================
   2. C strings at one address, and the views a walk keeps
   ========================================================================== *)

Lemma acstr_at_unique : forall segs m p s s', acstr_at segs m p s -> acstr_at segs m p s' -> s = s'.
Proof.
intros segs m p s s' ((_ & _ & H1) & N1) ((_ & _ & H2) & N2).
assert (Hlen : length s = length s').
{ destruct (Nat.lt_trichotomy (length s) (length s')) as [Hl | [Hl | Hl]]; [exfalso | exact Hl | exfalso].
  - pose proof (H1 (length s) ltac:(rewrite length_app; cbn [length]; lia)) as A.
    pose proof (H2 (length s) ltac:(rewrite length_app; cbn [length]; lia)) as Bq.
    rewrite A in Bq. rewrite nth_error_app2 in Bq by lia. rewrite Nat.sub_diag in Bq. cbn [nth_error] in Bq.
    rewrite nth_error_app1 in Bq by lia. symmetry in Bq. apply nth_error_In in Bq. exact (N2 Bq).
  - pose proof (H1 (length s') ltac:(rewrite length_app; cbn [length]; lia)) as A.
    pose proof (H2 (length s') ltac:(rewrite length_app; cbn [length]; lia)) as Bq.
    rewrite Bq in A. rewrite nth_error_app2 in A by lia. rewrite Nat.sub_diag in A. cbn [nth_error] in A.
    rewrite nth_error_app1 in A by lia. symmetry in A. apply nth_error_In in A. exact (N1 A). }
apply lw_list_ext; [exact Hlen|]. intros i Hi.
pose proof (H1 i ltac:(rewrite length_app; cbn [length]; lia)) as A.
pose proof (H2 i ltac:(rewrite length_app; cbn [length]; lia)) as Bq.
rewrite A in Bq. rewrite nth_error_app1 in Bq by lia. rewrite nth_error_app1 in Bq by lia. exact Bq.
Qed.

Lemma astr_arg_unique : forall segs m p o o', astr_arg segs m p o -> astr_arg segs m p o' -> o = o'.
Proof.
intros segs m p [s|] [s'|] H1 H2; unfold astr_arg in H1, H2.
- f_equal. exact (acstr_at_unique segs m p s s' (proj2 H1) (proj2 H2)).
- exfalso. exact (proj1 H1 H2).
- exfalso. exact (proj1 H2 H1).
- reflexivity.
Qed.

Lemma nth_error_some_nth : forall (l : list byte) n d, (n < length l)%nat -> nth_error l n = Some (nth n l d).
Proof. induction l as [|x l IH]; intros [|n] d H; cbn in *; try lia; [reflexivity | apply IH; lia]. Qed.

Lemma aview_some_grow : forall segs H m m' a,
  mem_grows (mrestrict H m) (mrestrict H m') -> aview segs H m a <> None -> aview segs H m' a <> None.
Proof.
intros segs H m m' a Hg Hn. unfold aview, mbyte in *.
destruct (mrestrict H m' (Z_to_bv 64 a)) eqn:E2; [discriminate|].
destruct (mrestrict H m (Z_to_bv 64 a)) eqn:E1; [|exact Hn].
exfalso. apply (Hg (Z_to_bv 64 a)); [rewrite E1; discriminate | exact E2].
Qed.

Lemma grows_of_present : forall H m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Eh; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)).
{ unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Lemma le_byte_1_0 : forall v, YO0f.le_byte v 1 0 = v mod 256.
Proof.
intros v. transitivity ((v mod 256) mod 256); [reflexivity | apply Z.mod_mod; lia].
Qed.

Lemma val_mem1_of_mbyte : forall segs m a b, mbyte segs m a = Some b -> val_mem segs m a 1 (bv_unsigned b).
Proof.
intros segs m a b Hb k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb. f_equal.
pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite le_byte_1_0, Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma md_fds_wvb : forall {fx : YK11.FPState} l X (m : Model), m_fds (with_vm_backing l X m) = m_fds m.
Proof. intros fx l X m. exact (proj1 (wvb_fds_fs l X m)). Qed.
Lemma md_fs_wvb : forall {fx : YK11.FPState} l X (m : Model), m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros fx l X m. exact (proj2 (wvb_fds_fs l X m)). Qed.

Lemma br_eq_atom : forall E n x, ew E n = x ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (bv_unsigned x =? 0).
Proof.
intros E n x Hn. rewrite branch_eq_U. pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
rewrite (U_atom E n (bv_unsigned x)) by first [rewrite Hn; symmetry; apply Z_to_bv_bv_unsigned | lia].
rewrite U_lit by lia. reflexivity.
Qed.

Lemma aarg_reg0 : forall regs, aarg regs 0 = bv_unsigned (getr regs 10).
Proof.
intros regs. unfold aarg, argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
reflexivity.
Qed.
Lemma aarg_reg1 : forall regs, aarg regs 1 = bv_unsigned (getr regs 11).
Proof.
intros regs. unfold aarg, argZ. replace (Z_to_bv 5 (10 + 1)) with (11%bv : bv 5) by (apply bv_eq; reflexivity).
reflexivity.
Qed.

Lemma dec_c0 : forall al : option (list byte), exists c,
  c = match al with Some t => bv_unsigned (nth 0 (t ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) | None => 0 end /\ 0 <= c <= 255.
Proof.
intros [t|]; eexists; (split; [reflexivity|]); [|lia].
pose proof (bv_unsigned_in_range 8 (nth 0 (t ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as Hr.
change (bv_modulus 8) with 256 in Hr. lia.
Qed.

Lemma acstr_first : forall segs m p t, acstr_at segs m p t -> mbyte segs m p = Some (nth 0 (t ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof.
intros segs m p t ((_ & _ & Hb) & _). pose proof (Hb 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as H0.
rewrite Z.add_0_r in H0. rewrite H0. destruct t; reflexivity.
Qed.

(* the index of the frame region (base atom 2) in a symbolic memory *)
Fixpoint stk_idx (rs : smem) : nat :=
  match rs with
  | [] => 0
  | r :: rs' => match r_base r with Some 2%nat => 0 | _ => S (stk_idx rs') end
  end.

(* ==========================================================================
   3. The symbolic entry state
   ========================================================================== *)

Definition DSB : Z := 0x7fff8000.
Definition dBx : sv := SOff 32 0.
Definition dSpan : Z * Z := (DSB, DSB + 2 ^ 44 - 1).
Definition d_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32].
Definition d_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 (2 ^ 47 - 1) 0); (32%nat, mkAF DSB DSB 0);
           (33%nat, mkAF 0 255 0)] [] [].
Definition d_ss (af : Z) : sstate := mkSS af sr_atoms d_regions None d_facts.
Definition d_SH : list shent := [mkSHE 11 0 1].
Definition alias_region : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition d_extra (c : Z) : list word := [Z_to_bv 64 DSB; Z_to_bv 64 c].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TL : PALib B.
Hypothesis HV : LinkVals (L := link_listing).
Hypothesis STRNCMP : RtString.astrncmp_realizes pa_segs B (pa_sigma LS___interceptor_trampoline_strncmp).
Hypothesis STRCMP : RtString.astrcmp_realizes pa_segs B (pa_sigma LS___interceptor_trampoline_strcmp).

Lemma ew_img : forall E n, img_env pa_val A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> ew E n = Z_to_bv 64 (pa_val n).
Proof. intros E n HE Hn. rewrite <- (HE n Hn). symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma st_ok_pi_submem : forall E ss ms rs,
  st_ok_pi pa_segs pa_val E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi pa_segs pa_val E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms rs HS Hs Hw. exact (st_ok_submem pa_segs E (abs_ss pa_val ss) ms rs HS Hs Hw). Qed.

(* the journal's bounds a walk needs: the window is above the allocator's ceiling and below 2 ^ 47 *)
Lemma aj_bounds : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  alloc_ceiling <= sp0 - STK /\ sp0 <= 2 ^ 47 /\ 0 <= XO /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (HSTK & HXO & (memS & HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
split; [lia|]. split; [lia|]. split; [exact HXO|]. intros a Ha. apply Hpres. lia.
Qed.

(* The kept views of a string the Pre states, at a later memory of the walk. *)
Section keep.
Variables (W : world pa_segs) (regs : bvmap 5 word) (memc memT : word -> option byte).
Hypothesis Hceil : alloc_ceiling <= spZ regs - DECIDE_AK.
Hypothesis UN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - DECIDE_AK <= a < spZ regs) ->
  aview pa_segs (w_H W) memT a = aview pa_segs (w_H W) memc a.
Hypothesis GR : mem_grows (rdW W memc) (rdW W memT).

Lemma ra_keep : forall p n,
  0 <= p -> p + n <= 2 ^ 47 ->
  range_addressable (ard pa_segs (rdW W memc)) SHADOW_OFF p n ->
  range_addressable (aview pa_segs (w_H W) memT) SHADOW_OFF p n.
Proof.
intros p n Hp Hpn HR. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : DECIDE_AK = 8208) by reflexivity.
apply (ra_shadow_eq (aview pa_segs (w_H W) memc)); [exact HR|].
intros x Hx. apply UN; unfold shadow_addr, SHADOW_OFF; lia.
Qed.

Lemma astr_keep : forall p s,
  acstr_at pa_segs (rdW W memc) p s -> apart_frame regs DECIDE_AK p (Z.of_nat (length s) + 1) ->
  0 <= p -> p + Z.of_nat (length s) + 1 <= 2 ^ 64 ->
  astr_at pa_segs W memT p s.
Proof.
intros p s ((_ & _ & Hb) & Hnz) Hap Hp Hp64. split; [|exact Hnz].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite UN by (unfold apart_frame in Hap; lia).
unfold aview. rewrite (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
rewrite (nth_error_some_nth _ _ (Z_to_bv 8 0)) by (rewrite length_app; cbn [length]; lia). reflexivity.
Qed.

Lemma aread_keep : forall regsT p s n,
  acstr_at pa_segs (rdW W memc) p s -> astr_rt_ok pa_segs regs DECIDE_AK (rdW W memc) p s ->
  spZ regsT = spZ regs - 16 -> 0 < n <= Z.of_nat (length s) + 1 ->
  aread_ok pa_segs (2 * ESTACK) W regsT memT p n.
Proof.
intros regsT p s n ((_ & _ & Hb) & Hnz) (Hp & Hl31 & Hamr & Hra & Hhv & Htl & Hap) HspT Hn.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : DECIDE_AK = 8208) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hp47 : p + Z.of_nat (length s) + 8 <= 2 ^ 47 - 1) by (unfold amem_range in Hamr; lia).
unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
- intros a Ha. split.
  + apply (aview_some_grow _ _ _ _ _ GR). unfold aview.
    replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
    rewrite (Hb (Z.to_nat (a - p)) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite (nth_error_some_nth _ _ (Z_to_bv 8 0)) by (rewrite length_app; cbn [length]; lia). cbn [option_map]. discriminate.
  + unfold ascratch_stk. rewrite HspT. unfold apart_frame in Hap. lia.
- split; [unfold amem_range in *; lia|]. split.
  + apply ra_keep; [lia | lia |]. intros x Hx. apply Hra. lia.
  + intros _ x Hx. apply (aview_some_grow _ _ _ _ _ GR). exact (Hhv x ltac:(unfold shadow_addr in *; lia)).
Qed.

Lemma atail_keep : forall p s,
  astr_rt_ok pa_segs regs DECIDE_AK (rdW W memc) p s -> atail_vis pa_segs W memT (p + astr_len s).
Proof.
intros p s (_ & _ & _ & _ & _ & Htl & _) a Ha. apply (aview_some_grow _ _ _ _ _ GR). exact (Htl a Ha).
Qed.

Lemma rtrom_keep : forall rlo rhi, arodata_okP pa_segs rlo rhi B (aview pa_segs (w_H W) memc) ->
  rt_rom_view pa_segs B W memT.
Proof.
intros rlo rhi Hro a Hrom Hno Herr. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : DECIDE_AK = 8208) by reflexivity.
assert (Hi : in_img pa_segs a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
pose proof (pa_segs_low a Hi) as Hlow.
rewrite UN by lia. apply Hro; [left; exact Hrom | exact Hno | exact Herr].
Qed.
End keep.

(* The post of a wrapper call in the walk: the journal, the registers, the model, the answer, the views and
   presence. *)
Definition wpost G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc (W : world pa_segs) regsT memT mdT k raw
    (R : bvmap 5 word -> Prop) : world pa_segs -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom pa_segs)) md2 /\
    ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\ same_but_materialized mdT md2 /\ R regs2 /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
       aview pa_segs (w_H W) mem2 a = aview pa_segs (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a).

(* wrapper_strncmp (+0x44) with a0 = alias, a1 = the "reac-pw:" literal, a2 = 8: LinkWalk.v's aj_gx_strncmp_sm_at,
   its premises from the Pre. *)
Lemma dec_strncmp_call : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs regsT memT mdT raw
    p t q,
  acstr_at pa_segs (rdW W memc) p t -> astr_rt_ok pa_segs regs DECIDE_AK (rdW W memc) p t ->
  acstr_at pa_segs (rdW W memc) q S_PREFIX -> astr_rt_ok pa_segs regs DECIDE_AK (rdW W memc) q S_PREFIX ->
  gx_ok pa_segs B G ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  arodata_okP pa_segs rlo rhi B (aview pa_segs (w_H W) memc) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - DECIDE_AK -> spZ regs <= sp0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - DECIDE_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memT a = aview pa_segs (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W memT) ->
  spZ regsT = spZ regs - 16 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 p -> getr regsT 11 = w64 q -> getr regsT 12 = w64 8 ->
  SRr pa_segs W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_strncmp)) memT (seg_rom pa_segs)) mdT)
    (wpost G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W regsT memT mdT k raw
       (fun regs2 => getr regs2 10 = w64 0 <-> has_prefix t = true)).
Proof.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs regsT memT mdT raw p t q
  Hpt Hpt_rt Hqs Hqs_rt HG HJ HROD Hal16 Hwlo Hwhi UN GR HspT Hgp Htp Hra Hraw Hx Hy Hn.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : DECIDE_AK = 8208) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (aj_bounds G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k HJ) as (Hceil & H47 & HXO & _).
assert (Hceil' : alloc_ceiling <= spZ regs - DECIDE_AK) by lia.
pose proof Hpt_rt as (Hp0 & Hpl & Hpm & _ & _ & _ & Hpa).
pose proof Hqs_rt as (Hq0 & Hql & Hqm & _ & _ & _ & Hqa).
assert (Hp47 : p + Z.of_nat (length t) + 8 <= 2 ^ 47 - 1) by (unfold amem_range in Hpm; lia).
assert (Hq47 : q + Z.of_nat (length S_PREFIX) + 8 <= 2 ^ 47 - 1) by (unfold amem_range in Hqm; lia).
eapply SRr_mono.
{ exact (aj_gx_strncmp_sm_at SK pa_segs B LAWS pa_segs_low (pa_sigma LS___interceptor_trampoline_strncmp) STRNCMP
    G XO OUT W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k p q 8 t S_PREFIX raw
    HG HJ ltac:(rewrite HspT; lia) ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw Hx Hy Hn ltac:(lia) Hp0 Hq0
    (astr_keep W regs memc memT UN p t Hpt Hpa ltac:(lia) ltac:(lia))
    (astr_keep W regs memc memT UN q S_PREFIX Hqs Hqa ltac:(lia) ltac:(lia))
    (aread_keep W regs memc memT Hceil' UN GR regsT p t (Z.min 8 (astr_len t + 1)) Hpt Hpt_rt HspT ltac:(unfold astr_len; lia))
    Hpm
    (aread_keep W regs memc memT Hceil' UN GR regsT q S_PREFIX (Z.min 8 (astr_len S_PREFIX + 1)) Hqs Hqs_rt HspT
       ltac:(unfold astr_len; lia))
    Hqm
    (atail_keep W regs memc memT GR p t Hpt_rt) (atail_keep W regs memc memT GR q S_PREFIX Hqs_rt)
    (rtrom_keep W regs memc memT Hceil' UN rlo rhi HROD)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & Hfr & Hpres2 & Hs).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact Hs|].
split; [split; intros H0; [apply (strncmp_prefix_iff t (proj2 Hpt)); apply HQ; exact H0
                           | apply HQ; apply (strncmp_prefix_iff t (proj2 Hpt)); exact H0] |].
split; [exact Hfr | exact Hpres2].
Qed.

(* wrapper_strcmp (+0x60) with a0 = kind, a1 = the "vlan" literal. *)
Lemma dec_strcmp_call : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs regsT memT mdT raw
    p t q,
  acstr_at pa_segs (rdW W memc) p t -> astr_rt_ok pa_segs regs DECIDE_AK (rdW W memc) p t ->
  acstr_at pa_segs (rdW W memc) q S_VLAN -> astr_rt_ok pa_segs regs DECIDE_AK (rdW W memc) q S_VLAN ->
  gx_ok pa_segs B G ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  arodata_okP pa_segs rlo rhi B (aview pa_segs (w_H W) memc) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - DECIDE_AK -> spZ regs <= sp0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - DECIDE_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memT a = aview pa_segs (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W memT) ->
  spZ regsT = spZ regs - 16 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 p -> getr regsT 11 = w64 q ->
  SRr pa_segs W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_strcmp)) memT (seg_rom pa_segs)) mdT)
    (wpost G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W regsT memT mdT k raw
       (fun regs2 => getr regs2 10 = w64 0 <-> bl_eqb t S_VLAN = true)).
Proof.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs regsT memT mdT raw p t q
  Hpt Hpt_rt Hqs Hqs_rt HG HJ HROD Hal16 Hwlo Hwhi UN GR HspT Hgp Htp Hra Hraw Hx Hy.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : DECIDE_AK = 8208) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (aj_bounds G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k HJ) as (Hceil & H47 & HXO & _).
assert (Hceil' : alloc_ceiling <= spZ regs - DECIDE_AK) by lia.
pose proof Hpt_rt as (Hp0 & Hpl & Hpm & _ & _ & _ & Hpa).
pose proof Hqs_rt as (Hq0 & Hql & Hqm & _ & _ & _ & Hqa).
assert (Hp47 : p + Z.of_nat (length t) + 8 <= 2 ^ 47 - 1) by (unfold amem_range in Hpm; lia).
assert (Hq47 : q + Z.of_nat (length S_VLAN) + 8 <= 2 ^ 47 - 1) by (unfold amem_range in Hqm; lia).
eapply SRr_mono.
{ exact (aj_gx_strcmp_at SK pa_segs B LAWS pa_segs_low (pa_sigma LS___interceptor_trampoline_strcmp) STRCMP
    G XO OUT W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k p q t S_VLAN raw
    HG HJ ltac:(rewrite HspT; lia) ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw Hx Hy Hp0 Hq0
    (astr_keep W regs memc memT UN p t Hpt Hpa ltac:(lia) ltac:(lia))
    (astr_keep W regs memc memT UN q S_VLAN Hqs Hqa ltac:(lia) ltac:(lia))
    (aread_keep W regs memc memT Hceil' UN GR regsT p t (astr_len t + 1) Hpt Hpt_rt HspT ltac:(unfold astr_len; lia))
    (aread_keep W regs memc memT Hceil' UN GR regsT q S_VLAN (astr_len S_VLAN + 1) Hqs Hqs_rt HspT ltac:(unfold astr_len; lia))
    (atail_keep W regs memc memT GR p t Hpt_rt) (atail_keep W regs memc memT GR q S_VLAN Hqs_rt)
    (rtrom_keep W regs memc memT Hceil' UN rlo rhi HROD)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & Hfr & Hpres2 & Hs).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact Hs|].
split; [split; intros H0; [apply bl_eqb_iff; apply HQ; exact H0 | apply HQ; apply bl_eqb_iff; exact H0] |].
split; [exact Hfr | exact Hpres2].
Qed.

(* The symbolic entry state holds at the call. *)
Lemma dec_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs af c,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - DECIDE_AK -> spZ regs <= sp0 ->
  0 <= aarg regs 1 <= 2 ^ 47 - 1 -> 0 <= c <= 255 ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs (d_extra c))) (d_ss af)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (pa_val A_TEXT + af)) memc (seg_rom pa_segs))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs af c HJ Hal16 Hwlo Hwhi Ha1 Hc.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
destruct (aj_bounds G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as (Hceil & H47 & HXO & Hpres).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : DECIDE_AK = 8208) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 64 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
unfold PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP in HcellR, HgotR.
set (E := Eimg (Ereg regs (d_extra c))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (d_extra c)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 DSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (pa_val (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 64) = Z_to_bv 64 (pa_val (A_OBJ 64))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U11 : bv_unsigned (ew E 11) = aarg regs 1) by (rewrite E11, aarg_reg1; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold d_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold d_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable pa_segs). apply Hpres. lia.
  + fold E. rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 1)) 0 8 (SOff (A_OBJ 64) 0) (pa_val (A_OBJ 64)));
    [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 64)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VB (A_OBJ 64) (pa_val (A_OBJ 64)) Ecell) by (pose proof (pa_val_range (A_OBJ 64)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 64)) 0 8 (SOff 32 0) DSB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold DSB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold d_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
  rewrite (VB (A_OBJ 64) (pa_val (A_OBJ 64)) Ecell) by (pose proof (pa_val_range (A_OBJ 64)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hwlo Hwhi Hceil H47 C1a C1b HKv HcellR HgcD HgotR. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [d_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, U11, E32, E33, !unsigned_lit_small by (unfold DSB; lia).
  try change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  revert Hwlo Hwhi Hceil H47 C1a C1b HKv Hal16 Ha1 Hc. clear. unfold DSB. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the shadow entry of alias[0] (the check +0x18 .. +0x24) *)
Lemma dec_shok : forall (W : world pa_segs) Ex (m : word -> option byte) p n,
  ew Ex 32 = Z_to_bv 64 DSB -> ew Ex 11 = Z_to_bv 64 p -> 0 < p -> amem_range p n -> 1 <= n ->
  range_addressable (aview pa_segs (w_H W) m) SHADOW_OFF p 1 ->
  sh_ok pa_segs dBx d_SH Ex (rdW W m).
Proof.
intros W Ex m p n H32 H11 Hp Ham Hn HR. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hp47 : p < 2 ^ 47) by (unfold amem_range in Ham; lia).
unfold sh_ok, d_SH. apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold dBx.
rewrite (U_atom Ex 32 DSB H32) by (unfold DSB; lia). rewrite (U_atom Ex 11 p H11) by lia.
split.
- rewrite Z.add_0_r. replace (1 - 0) with 1 by lia. rewrite <- (aview_rd_of pa_segs). exact HR.
- intros a Ha. cbn [Z.min Z.max] in Ha. unfold amem_range, DSB in *. lia.
Qed.

(* ==========================================================================
   4. The walk: one script for both entries
   ========================================================================== *)

Ltac dec_env_of HS :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?En _ _ => En
  | st_ok _ ?En _ _ => En
  end.

Ltac dec_usp Ex Usp :=
  let regs := ident:(regs) in
  let EA := ident:(EA) in
  let Usp0 := ident:(Usp0) in
  assert (Usp : bv_unsigned (ew Ex 2) = spZ regs)
    by (let EA1 := fresh "EA1" in destruct EA as [EA1 _]; try rewrite (EA1 2%nat ltac:(lia)); exact Usp0).

(* the run's writes: the frame [sp - 16, sp), an awr_byte of the journal's own window *)
Ltac dec_awr :=
  let Ha := ident:(Ha) in
  lazymatch goal with |- awr_ok_x ?Ex ?rs _ _ _ _ _ _ _ _ _ _ =>
    let Usp := fresh "Usp" in dec_usp Ex Usp;
    let rs' := eval vm_compute in rs in try change rs with rs';
    repeat first
    [ apply awr_ok_x_nil
    | apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
        let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; rewrite ?Usp in Ha;
        first [ lia | left; split; [unfold awr_byte; left; lia | lia] ]
      | ] ]
  end.

(* the windows of a run lie in [sp - K, sp) *)
Ltac dec_win Ex :=
  let Usp := fresh "Usp" in dec_usp Ex Usp;
  let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros bb wl wh a Hin Hrr; cbv beta; vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
  destruct Hin.

(* after a run with tokens, name the extended environment and carry its agreement with E *)
Ltac dec_env :=
  let E := ident:(E) in
  let EA := ident:(EA) in
  let HS := ident:(HS) in
  let E2 := ident:(E2) in
  let En := dec_env_of HS in
  lazymatch En with
  | ewset _ _ _ =>
      let E2 := fresh "En" in let HE2 := fresh "HEn" in
      remember En as E2 eqn:HE2;
      let EA2 := fresh "EA" in
      assert (EA2 : env_agree 34 E E2)
        by (rewrite HE2; let EA1 := fresh "EA1" in let EA3 := fresh "EA3" in destruct EA as [EA1 EA3];
            split; [intros nn Hnn; repeat rewrite ew_ewset_other by lia; exact (EA1 nn Hnn) | exact EA3]);
      clear HE2 EA; rename EA2 into EA
  | _ => idtac
  end.

(* after a run: the kept views, presence and model, from the run's frame *)
Ltac dec_step :=
  let regs := ident:(regs) in
  let memc := ident:(memc) in
  let mdc := ident:(mdc) in
  let W := ident:(W) in
  let UN := ident:(UN) in
  let GR := ident:(GR) in
  let FD := ident:(FD) in
  let HJ := ident:(HJ) in
  let HF := ident:(HF) in
  let HG := ident:(HG) in
  let Ha := ident:(Ha) in
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?Hh ?M) (mrestrict ?Hh ?M') |- _ =>
    let KF := fresh "KF" in
    assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - DECIDE_AK <= a < spZ regs) ->
              aview pa_segs (w_H W) M' a = aview pa_segs (w_H W) M a)
      by (apply (kept_of_frame (segs := pa_segs) Ex rs (w_H W) M M' (fun a => spZ regs - DECIDE_AK <= a < spZ regs) HFr);
          dec_win Ex);
    let UN2 := fresh "UN" in
    assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - DECIDE_AK <= a < spZ regs) ->
              aview pa_segs (w_H W) M' a = aview pa_segs (w_H W) memc a)
      by (intros a Hai Hn; rewrite (KF a Hai Hn); exact (UN a Hai Hn));
    let GR2 := fresh "GR" in
    assert (GR2 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) M')) by (intros x Hx; apply HG; apply GR; exact Hx);
    clear KF UN GR HF HFr HG; rename UN2 into UN; rename GR2 into GR
  end;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let FD2 := fresh "FD" in
    assert (FD2 : m_fds mdx = m_fds mdc /\ m_fs mdx = m_fs mdc)
      by (rewrite ?md_fds_wvb, ?md_fs_wvb; rewrite ?md_fds_wvb, ?md_fs_wvb in FD; exact FD);
    clear FD; rename FD2 into FD
  end;
  rewrite ?wvb_collapse in HJ;
  dec_env.

Ltac dec_run :=
  let HS := ident:(HS) in
  let HJ := ident:(HJ) in
  let SHOK := ident:(SHOK) in
  let RUN := ident:(RUN) in
  let rhi := ident:(rhi) in
  let rhi := ident:(rhi) in paj_run_tok RUN HS HJ SHOK dSpan; [dec_awr | dec_step].
Ltac dec_branch :=
  let HS := ident:(HS) in
  let SHOK := ident:(SHOK) in
  let RUN := ident:(RUN) in
  let BR := ident:(BR) in
  let rhi := ident:(rhi) in
  let rhi := ident:(rhi) in psrr_branch_tok RUN BR HS SHOK dSpan.

(* the branch condition on an atom below 34, from the entry registers *)
Ltac dec_hc_atom n x :=
  let EA := ident:(EA) in
  let HS := ident:(HS) in
  let Hc := ident:(Hc) in
  let Ex := dec_env_of HS in
  rewrite (br_eq_atom Ex n x) in Hc
    by (let EA1 := fresh "EA1" in destruct EA as [EA1 _]; try rewrite (EA1 n ltac:(lia)); assumption).

(* the registers at a wrapper call *)
Ltac dec_call_facts :=
  let regs := ident:(regs) in
  let EA := ident:(EA) in
  let HS := ident:(HS) in
  let Hgp := ident:(Hgp) in
  let Htp := ident:(Htp) in
  let E3 := ident:(E3) in
  let E4 := ident:(E4) in
  let Qsp := ident:(Qsp) in
  let Qgp := ident:(Qgp) in
  let Qtp := ident:(Qtp) in
  let R1 := ident:(R1) in
  let R2 := ident:(R2) in
  let R3 := ident:(R3) in
  let R4 := ident:(R4) in
  let R10 := ident:(R10) in
  let R11 := ident:(R11) in
  pmkst HS;
  prreg HS (1%bv : bv 5) R1; prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
  prreg HS (10%bv : bv 5) R10; prreg HS (11%bv : bv 5) R11;
  lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?ms) |- _ =>
    let Usp := fresh "Usp" in dec_usp Ex Usp;
    let HEIx := lazymatch goal with H : img_env _ _ Ex |- _ => H end in
    rewrite (ew_img Ex _ HEIx) in R11 by (unfold A_TEXT, A_LIM; lia);
    assert (Qsp : spZ (ms_regs ms) = spZ regs - 16)
      by (unfold spZ at 1; rewrite R2, Usp, unsigned_lit_small by lia; lia);
    assert (Qgp : getr (ms_regs ms) 3 = w64 (as_gp B))
      by (rewrite R3; let EA1 := fresh "EA1" in destruct EA as [EA1 _]; try rewrite (EA1 3%nat ltac:(lia)); rewrite E3; exact Hgp);
    assert (Qtp : getr (ms_regs ms) 4 = w64 (as_tp B))
      by (rewrite R4; let EA1 := fresh "EA1" in destruct EA as [EA1 _]; try rewrite (EA1 4%nat ltac:(lia)); rewrite E4; exact Htp);
    let EA1 := fresh "EA1" in pose proof (proj1 EA) as EA1; try rewrite EA1 in R10 by lia; clear EA1
  end.

(* after a wrapper call: the frame region kept, the havoc'd environment, the invariants at the call's end *)
Ltac dec_after_call :=
  let regs := ident:(regs) in
  let memc := ident:(memc) in
  let mdc := ident:(mdc) in
  let W := ident:(W) in
  let E := ident:(E) in
  let EA := ident:(EA) in
  let UN := ident:(UN) in
  let GR := ident:(GR) in
  let FD := ident:(FD) in
  let HS := ident:(HS) in
  let HJ := ident:(HJ) in
  let SHOK := ident:(SHOK) in
  let HEI := ident:(HEI) in
  let E3 := ident:(E3) in
  let Ha := ident:(Ha) in
  let Hres := ident:(Hres) in
  let A44 := ident:(A44) in
  let Qsp := ident:(Qsp) in
  let Qgp := ident:(Qgp) in
  let Qtp := ident:(Qtp) in
  let R1 := ident:(R1) in
  let R2 := ident:(R2) in
  let R3 := ident:(R3) in
  let R4 := ident:(R4) in
  let R10 := ident:(R10) in
  let R11 := ident:(R11) in
  let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in
  let md2 := fresh "md2" in let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in let Hsbm := fresh "Hsbm" in
  let Heff := fresh "Heff" in let Hpres2 := fresh "Hpres2" in
  cbv beta; unfold wpost;
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsbm & Hres & Heff & Hpres2);
  let UN2 := fresh "UN" in
  assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - DECIDE_AK <= a < spZ regs) ->
            aview pa_segs (w_H W) mem2 a = aview pa_segs (w_H W) memc a)
    by (intros a Hai Hn; rewrite (Heff a Hai ltac:(rewrite Qsp; lia)); exact (UN a Hai Hn));
  let GR2 := fresh "GR" in
  assert (GR2 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2))
    by (intros x Hx; apply (grows_of_present _ _ _ Hpres2); apply GR; exact Hx);
  let FD2 := fresh "FD" in
  assert (FD2 : m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc)
    by (rewrite (same_but_materialized_wvb _ _ Hsbm), md_fds_wvb, md_fs_wvb; exact FD);
  lazymatch goal with HS : st_ok _ ?Ex ?ssc _ |- _ =>
    let i := eval vm_compute in (stk_idx (ss_mem ssc)) in
    let Usp := fresh "Usp" in dec_usp Ex Usp;
    let HS2 := fresh "HS" in
    jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 (cons i nil) HS2;
    (match type of HS2 with ?tq -> _ => let HRK := fresh "HRK" in assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end);
    [ let a := fresh "a" in let Ha := fresh "Ha" in
      cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp;
      intros a Ha;
      [ apply (mbyte_of_aview pa_segs); apply Heff; [lia | rewrite Qsp; lia]
      | intros _; apply (apresent_writable pa_segs);
        let Hw := fresh "Hw" in
        destruct (aj_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (_ & _ & _ & Hw); apply Hw; lia ]
    | ];
    clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
    let E3 := fresh "Ec" in let HE3 := fresh "HEc" in
    remember (havoc Ex 40 (map (getr regs2) CLOB)) as E3 eqn:HE3 in HS;
    let HEI3 := fresh "HEI" in
    assert (HEI3 : img_env pa_val A_LIM E3) by (rewrite HE3; apply img_env_havoc; [assumption | cbv; lia]);
    assert (A44 : ew E3 44 = getr regs2 10) by (rewrite HE3; reflexivity);
    let EA3 := fresh "EA" in
    assert (EA3 : env_agree 34 E E3) by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact EA]);
    clear HE3 EA; rename EA3 into EA;
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in try change ss3 with v in HS end;
    clear SHOK; assert (SHOK : sh_ok pa_segs dBx [] E3 (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil);
    clear UN GR FD HJ Heff Hpres2 Hsbm Qsp Qgp Qtp R1 R2 R3 R4 R10 R11;
    rename UN2 into UN; rename GR2 into GR; rename FD2 into FD; rename HJ2 into HJ
  end.

(* the return: paj_ret_at, then apost_leaf; tval proves the result word *)
Ltac dec_finish tval :=
  let regs := ident:(regs) in
  let W := ident:(W) in
  let EA := ident:(EA) in
  let UN := ident:(UN) in
  let GR := ident:(GR) in
  let FD := ident:(FD) in
  let HS := ident:(HS) in
  let HJ := ident:(HJ) in
  let HJc := ident:(HJc) in
  let Hraw := ident:(Hraw) in
  let HAE := ident:(HAE) in
  let E1 := ident:(E1) in
  let Ha := ident:(Ha) in
  let Hk' := ident:(Hk') in
  let Ha' := ident:(Ha') in
  let c0 := ident:(c0) in
  let RR1 := ident:(RR1) in
  let RR10 := ident:(RR10) in
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    prreg HS (1%bv : bv 5) RR1; prreg HS (10%bv : bv 5) RR10;
    let HAE2 := fresh "HAE" in
    assert (HAE2 : env_agree 32 (Ereg regs (d_extra c0)) Ex)
      by (let EA1 := fresh "EA1" in let EA2 := fresh "EA2" in let HAE1 := fresh "HAE1" in let HAE3 := fresh "HAE3" in
          destruct EA as [EA1 EA2]; destruct HAE as [HAE1 HAE3]; split;
          [intros nn Hnn; try rewrite (EA1 nn ltac:(lia)); exact (HAE1 nn Hnn) | congruence]);
    let HPr := fresh "HPr" in
    pose proof (aregs_preserved_of_st_ok pa_segs (w_H W) Ex (abs_ss pa_val ssx) msx regs (d_extra c0) HS HAE2
      ltac:(vm_compute; reflexivity)) as HPr;
    eapply (paj_ret_at (PL := PL_link) W Ex ssx msx mdx _ HS eq_refl ltac:(vm_compute; reflexivity));
    let mat := fresh "mat" in intros mat;
    replace (v_jalr (getr (ms_regs msx) 1) 0) with (getr regs 1)
      by (rewrite RR1; let EA1 := fresh "EA1" in destruct EA as [EA1 _]; try rewrite (EA1 1%nat ltac:(lia)); rewrite E1;
          symmetry; exact Hraw);
    eapply (apost_leaf SK pa_segs B LAWS pa_segs_low);
    [ exact HJc
    | apply (ajournal_gx_materialize pa_segs B LAWS pa_segs_low); exact HJ
    | lia | lia | lia
    | rewrite md_fds_wvb; exact (proj1 FD)
    | rewrite md_fs_wvb; exact (proj2 FD)
    | exact HPr
    | let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn _; exact (UN a Ha Hn)
    | let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; exact (apresent_grows _ _ _ a GR Hp)
    | let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in intros a Ha;
      destruct (aj_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (_ & _ & _ & Hw); apply Hw; lia
    | let x := fresh "x" in let Hx := fresh "Hx" in let rr := fresh "rr" in let Hrr := fresh "Hrr" in
      intros x Hx; destruct Hx as (rr & Hrr & _); destruct Hrr
    | split; [symmetry; apply set_fs_self|]; split; [apply Permutation_refl|];
      unfold decide_apost;
      let k1 := fresh "k1" in let al1 := fresh "al1" in let Hk1 := fresh "Hk1" in let Ha1 := fresh "Ha1" in
      intros k1 al1 Hk1 Ha1;
      rewrite (astr_arg_unique _ _ _ _ _ Hk1 Hk'), (astr_arg_unique _ _ _ _ _ Ha1 Ha'), RR10; tval ]
  end.

(* the kind arm from +0x54 (alias NULL or empty): Hdec says what `decide` is there *)
Ltac dec_kind :=
  let regs := ident:(regs) in
  let memc := ident:(memc) in
  let W := ident:(W) in
  let UN := ident:(UN) in
  let GR := ident:(GR) in
  let HJ := ident:(HJ) in
  let Hc := ident:(Hc) in
  let Hal16 := ident:(Hal16) in
  let Hwlo := ident:(Hwlo) in
  let Hwhi := ident:(Hwhi) in
  let HGX := ident:(HGX) in
  let HROD := ident:(HROD) in
  let E10 := ident:(E10) in
  let k0 := ident:(k0) in
  let Hk := ident:(Hk) in
  let Hk_rt := ident:(Hk_rt) in
  let Hvl := ident:(Hvl) in
  let Hvl_rt := ident:(Hvl_rt) in
  let kt := ident:(kt) in
  let Hkt := ident:(Hkt) in
  let Hkt_rt := ident:(Hkt_rt) in
  let Hdec := ident:(Hdec) in
  let Hres := ident:(Hres) in
  let A44 := ident:(A44) in
  let Qsp := ident:(Qsp) in
  let Qgp := ident:(Qgp) in
  let Qtp := ident:(Qtp) in
  let R1 := ident:(R1) in
  let R10 := ident:(R10) in
  let R11 := ident:(R11) in
  let G := ident:(G) in
  let XO := ident:(XO) in
  let OUT := ident:(OUT) in
  let STK := ident:(STK) in
  let sp0 := ident:(sp0) in
  let FP := ident:(FP) in
  let ly := ident:(ly) in
  let S := ident:(S) in
  let W0 := ident:(W0) in
  let mem0 := ident:(mem0) in
  let md0 := ident:(md0) in
  let own := ident:(own) in
  let lyc := ident:(lyc) in
  let Sc := ident:(Sc) in
  let k := ident:(k) in
  let rlo := ident:(rlo) in
  let rhi := ident:(rhi) in
  dec_branch;
  [ (* +0x54 taken: kind is NULL; +0x68 a0 := V_MARK *)
    dec_hc_atom 10%nat (getr regs 10); rewrite <- aarg_reg0 in Hc; apply Z.eqb_eq in Hc;
    destruct k0 as [kt|]; [exfalso; unfold astr_arg in Hk; exact (proj1 Hk Hc) |]; clear Hc;
    dec_run; dec_finish ltac:(rewrite Hdec; reflexivity)
  | (* +0x58 .. +0x60: strcmp(kind, "vlan") *)
    dec_hc_atom 10%nat (getr regs 10); rewrite <- aarg_reg0 in Hc; apply Z.eqb_neq in Hc;
    destruct k0 as [kt|]; [| unfold astr_arg in Hk; exfalso; exact (Hc Hk)]; clear Hc;
    unfold astr_arg in Hk; destruct Hk as [_ Hkt]; pose proof (Hk_rt kt eq_refl) as Hkt_rt;
    dec_run; dec_call_facts;
    eapply SRr_bind;
    [ eapply (dec_strcmp_call rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs);
      [ exact Hkt | exact Hkt_rt | exact Hvl | exact Hvl_rt | exact HGX | exact HJ | exact HROD
      | exact Hal16 | exact Hwlo | exact Hwhi | exact UN | exact GR | exact Qsp | exact Qgp | exact Qtp
      | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
      | rewrite R10, E10, aarg_reg0; unfold w64; symmetry; apply Z_to_bv_bv_unsigned
      | rewrite R11; reflexivity ]
    | dec_after_call; dec_run; dec_branch;
      [ (* +0x64 taken: kind is "vlan"; +0x78 a0 := V_LEAVE_VLAN *)
        rewrite (br_eq_atom _ 44 _ A44) in Hc; apply Z.eqb_eq in Hc;
        assert (Hv : bl_eqb kt S_VLAN = true) by (apply Hres; apply bv_eq; rewrite Hc; reflexivity); clear Hc;
        dec_run; dec_finish ltac:(rewrite Hdec; cbv beta iota; rewrite Hv; reflexivity)
      | (* +0x68 a0 := V_MARK *)
        rewrite (br_eq_atom _ 44 _ A44) in Hc; apply Z.eqb_neq in Hc;
        assert (Hv : bl_eqb kt S_VLAN = false)
          by (apply Bool.not_true_is_false; let Hb := fresh "Hb" in intros Hb; apply Hc; rewrite (proj2 Hres Hb); reflexivity);
        clear Hc; dec_run; dec_finish ltac:(rewrite Hdec; cbv beta iota; rewrite Hv; reflexivity) ] ] ].

Ltac dec_setup af :=
  let regs := ident:(regs) in
  let memc := ident:(memc) in
  let mdc := ident:(mdc) in
  let W := ident:(W) in
  let E := ident:(E) in
  let EA := ident:(EA) in
  let Usp0 := ident:(Usp0) in
  let UN := ident:(UN) in
  let GR := ident:(GR) in
  let FD := ident:(FD) in
  let HS := ident:(HS) in
  let HJ := ident:(HJ) in
  let HJc := ident:(HJc) in
  let SHOK := ident:(SHOK) in
  let RUN := ident:(RUN) in
  let BR := ident:(BR) in
  let HEI := ident:(HEI) in
  let Hraw := ident:(Hraw) in
  let Hgp := ident:(Hgp) in
  let Htp := ident:(Htp) in
  let Hal16 := ident:(Hal16) in
  let Hwlo := ident:(Hwlo) in
  let Hwhi := ident:(Hwhi) in
  let HGX := ident:(HGX) in
  let HROD := ident:(HROD) in
  let HAE := ident:(HAE) in
  let E1 := ident:(E1) in
  let E2 := ident:(E2) in
  let E3 := ident:(E3) in
  let E4 := ident:(E4) in
  let E10 := ident:(E10) in
  let E11 := ident:(E11) in
  let E32 := ident:(E32) in
  let E33 := ident:(E33) in
  let k0 := ident:(k0) in
  let al0 := ident:(al0) in
  let Hk := ident:(Hk) in
  let Ha := ident:(Ha) in
  let Hk' := ident:(Hk') in
  let Ha' := ident:(Ha') in
  let Hk_rt := ident:(Hk_rt) in
  let Ha_rt := ident:(Ha_rt) in
  let Hpx := ident:(Hpx) in
  let Hpx_rt := ident:(Hpx_rt) in
  let Hvl := ident:(Hvl) in
  let Hvl_rt := ident:(Hvl_rt) in
  let c0 := ident:(c0) in
  let Hc0def := ident:(Hc0def) in
  let Hc0 := ident:(Hc0) in
  let Hceil' := ident:(Hceil') in
  let Hceil := ident:(Hceil) in
  let H47 := ident:(H47) in
  let HXO := ident:(HXO) in
  let Hwin := ident:(Hwin) in
  let HKv := ident:(HKv) in
  let Hes := ident:(Hes) in
  let Ha1r := ident:(Ha1r) in
  let t := ident:(t) in
  let Hra4 := ident:(Hra4) in
  let Hev := ident:(Hev) in
  let Hside := ident:(Hside) in
  let Hwr := ident:(Hwr) in
  let C1a := ident:(C1a) in
  let C1b := ident:(C1b) in
  let C2 := ident:(C2) in
  let C3 := ident:(C3) in
  let C4 := ident:(C4) in
  let C5 := ident:(C5) in
  let G := ident:(G) in
  let XO := ident:(XO) in
  let OUT := ident:(OUT) in
  let STK := ident:(STK) in
  let sp0 := ident:(sp0) in
  let FP := ident:(FP) in
  let ly := ident:(ly) in
  let S := ident:(S) in
  let W0 := ident:(W0) in
  let mem0 := ident:(mem0) in
  let md0 := ident:(md0) in
  let own := ident:(own) in
  let lyc := ident:(lyc) in
  let Sc := ident:(Sc) in
  let k := ident:(k) in
  let HEdef := ident:(HEdef) in
  let EL := ident:(EL) in
  let HPRE := ident:(HPRE) in
  let HRD := ident:(HRD) in
  let HP := ident:(HP) in
  let rlo := ident:(rlo) in
  let rhi := ident:(rhi) in
  intros rlo rhi; unfold decide_acontract_at, aleaf_rd;
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HRD HP;
  clear HRD;
  destruct HPRE as (HJ & HGX & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hwr);
  clear Hra4 Hev Hside Hwr;
  destruct HP as (k0 & al0 & Hk & Ha & Hpx & Hpx_rt & Hvl & Hvl_rt & Hk_rt & Ha_rt);
  pose proof Hk as Hk'; pose proof Ha as Ha'; pose proof HJ as HJc;
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5);
  assert (HKv : DECIDE_AK = 8208) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
  destruct (aj_bounds G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as (Hceil & H47 & HXO & Hwin);
  assert (Hceil' : alloc_ceiling <= spZ regs - DECIDE_AK) by lia;
  destruct (dec_c0 al0) as (c0 & Hc0def & Hc0);
  assert (Ha1r : 0 <= aarg regs 1 <= 2 ^ 47 - 1) by
    (destruct al0 as [t|]; unfold astr_arg in Ha;
     [ destruct (Ha_rt t eq_refl) as (Hp & _ & Hamr & _); unfold amem_range in Hamr; lia | rewrite Ha; lia ]);
  pose proof (dec_entry G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs af c0 HJ Hal16 Hwlo Hwhi
    Ha1r Hc0) as HS;
  remember (Eimg (Ereg regs (d_extra c0))) as E eqn:HEdef;
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env);
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (d_extra c0)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn);
  assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl));
  assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl));
  assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl));
  assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl));
  assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl));
  assert (E32 : ew E 32 = Z_to_bv 64 DSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0));
  assert (E33 : ew E 33 = Z_to_bv 64 c0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1));
  assert (HAE : env_agree 32 (Ereg regs (d_extra c0)) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]);
  assert (EA : env_agree 34 E E) by (split; [intros; reflexivity | reflexivity]);
  assert (Usp0 : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity);
  clear HEdef EL;
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - DECIDE_AK <= a < spZ regs) ->
            aview pa_segs (w_H W) memc a = aview pa_segs (w_H W) memc a) by (intros; reflexivity);
  assert (GR : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by (intros x Hx; exact Hx);
  assert (FD : m_fds mdc = m_fds mdc /\ m_fs mdc = m_fs mdc) by (split; reflexivity);
  assert (SHOK : sh_ok pa_segs dBx [] E (mrestrict (w_H W) (ms_mem (mkst regs (Z_to_bv 64 (pa_val A_TEXT + af)) memc (seg_rom pa_segs))))) by (unfold sh_ok; apply Forall_nil);
  pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN;
  pose proof (paj_branch (PI := PI)) as BR;
  unfold cfg_at; change (YG0d.w64 (pa_val A_TEXT + af)) with (Z_to_bv 64 (pa_val A_TEXT + af)).

(* alias is a string (+0x08 not taken): the shadow entry of alias[0] for the check, then +0x0c .. +0x28 *)
Ltac dec_alias :=
  let regs := ident:(regs) in
  let memc := ident:(memc) in
  let W := ident:(W) in
  let EA := ident:(EA) in
  let UN := ident:(UN) in
  let HS := ident:(HS) in
  let SHOK := ident:(SHOK) in
  let Hc := ident:(Hc) in
  let E11 := ident:(E11) in
  let E32 := ident:(E32) in
  let al0 := ident:(al0) in
  let Ha := ident:(Ha) in
  let Ha_rt := ident:(Ha_rt) in
  let Hc0def := ident:(Hc0def) in
  let Hceil' := ident:(Hceil') in
  let t := ident:(t) in
  let Hat := ident:(Hat) in
  let Hat_rt := ident:(Hat_rt) in
  dec_hc_atom 11%nat (getr regs 11); rewrite <- aarg_reg1 in Hc; apply Z.eqb_neq in Hc;
  destruct al0 as [t|]; [ | unfold astr_arg in Ha; exfalso; exact (Hc Ha)]; clear Hc;
  unfold astr_arg in Ha; destruct Ha as [_ Hat]; pose proof (Ha_rt t eq_refl) as Hat_rt; clear Ha_rt;
  cbv beta iota in Hc0def;
  clear SHOK;
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict _ ?ms) |- _ =>
    assert (SHOK : sh_ok pa_segs dBx d_SH Ex (mrestrict (w_H W) (ms_mem ms)));
    [ apply (dec_shok W Ex (ms_mem ms) (aarg regs 1) (Z.of_nat (length t) + 8));
      [ let EA1 := fresh "EA1" in destruct EA as [EA1 _]; try rewrite (EA1 32%nat ltac:(lia)); exact E32
      | let EA1 := fresh "EA1" in destruct EA as [EA1 _]; try rewrite (EA1 11%nat ltac:(lia)); rewrite E11, aarg_reg1;
        symmetry; apply Z_to_bv_bv_unsigned
      | exact (proj1 Hat_rt) | exact (proj1 (proj2 (proj2 Hat_rt))) | lia
      | apply (ra_keep W regs memc (ms_mem ms) Hceil' UN); [lia | lia |];
        let x := fresh "x" in let Hx := fresh "Hx" in
        intros x Hx; apply (proj1 (proj2 (proj2 (proj2 Hat_rt)))); lia ]
    | ]
  end;
  dec_run.

(* +0x28: drop the two .got regions, add alias[0]'s region; then +0x28 .. +0x2c *)
Ltac dec_reshape :=
  let regs := ident:(regs) in
  let memc := ident:(memc) in
  let W := ident:(W) in
  let EA := ident:(EA) in
  let UN := ident:(UN) in
  let HS := ident:(HS) in
  let SHOK := ident:(SHOK) in
  let E11 := ident:(E11) in
  let E33 := ident:(E33) in
  let c0 := ident:(c0) in
  let Hc0def := ident:(Hc0def) in
  let Hat := ident:(Hat) in
  let Hat_rt := ident:(Hat_rt) in
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?ms) |- _ =>
    let i := eval vm_compute in (stk_idx (ss_mem ssx)) in
    let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
    let HS2 := fresh "HS" in
    pose proof (st_ok_pi_submem Ex ssx _ [r0] HS ltac:(cbn [ss_mem]; submem_tac) ltac:(vm_compute; reflexivity)) as HS2;
    clear HS;
    let Usp := fresh "Usp" in dec_usp Ex Usp;
    let U11 := fresh "U11" in
    assert (U11 : bv_unsigned (ew Ex 11) = aarg regs 1)
      by (let EA1 := fresh "EA1" in destruct EA as [EA1 _]; try rewrite (EA1 11%nat ltac:(lia)); rewrite E11, aarg_reg1; reflexivity);
    let HS3 := fresh "HS" in
    assert (HS3 : st_ok_pi pa_segs pa_val Ex
              (mkSS (ss_pc ssx) (ss_regs ssx) [alias_region; r0] (ss_resv ssx) (ss_facts ssx)) (restrict (w_H W) ms));
    [ apply (st_ok_pi_add_region Ex (mkSS (ss_pc ssx) (ss_regs ssx) [r0] (ss_resv ssx) (ss_facts ssx)) _ alias_region HS2 eq_refl);
      [ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks alias_region base_val ms_mem restrict];
        rewrite U11; split; [lia|]; split; [lia|]; split; [let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; lia|];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val pa_segs Ex _ (aarg regs 1) 0 1 (SOff 33 0) c0);
        [ cbn [sv_denot]; let EA1 := fresh "EA1" in destruct EA as [EA1 _]; try rewrite (EA1 33%nat ltac:(lia)); rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; lia | cbn; lia | ];
        rewrite Z.add_0_r, Hc0def; apply val_mem1_of_mbyte;
        rewrite (mbyte_of_aview pa_segs (w_H W) (w_H W) memc (ms_mem ms) (aarg regs 1)
                   (UN (aarg regs 1) ltac:(lia) ltac:(pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hat_rt)))))) as Hap; unfold apart_frame in Hap; lia)));
        exact (acstr_first _ _ _ _ Hat)
      | cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint;
        cbn [alias_region YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
        rewrite U11, Usp; split; [|exact I];
        pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hat_rt)))))) as Hap; unfold apart_frame in Hap; lia ]
    | ];
    clear HS2; rename HS3 into HS;
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in try change ss3 with v in HS end;
    clear SHOK; assert (SHOK : sh_ok pa_segs dBx [] Ex (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil)
  end;
  dec_run.

(* alias[0] is not NUL: strncmp(alias, "reac-pw:", 8) and the two answers *)
Ltac dec_prefix :=
  let regs := ident:(regs) in
  let memc := ident:(memc) in
  let W := ident:(W) in
  let UN := ident:(UN) in
  let GR := ident:(GR) in
  let HS := ident:(HS) in
  let HJ := ident:(HJ) in
  let Hc := ident:(Hc) in
  let Hal16 := ident:(Hal16) in
  let Hwlo := ident:(Hwlo) in
  let Hwhi := ident:(Hwhi) in
  let HGX := ident:(HGX) in
  let HROD := ident:(HROD) in
  let E11 := ident:(E11) in
  let Hpx := ident:(Hpx) in
  let Hpx_rt := ident:(Hpx_rt) in
  let c0 := ident:(c0) in
  let Hc0def := ident:(Hc0def) in
  let t := ident:(t) in
  let b := ident:(b) in
  let Hat := ident:(Hat) in
  let Hat_rt := ident:(Hat_rt) in
  let Hres := ident:(Hres) in
  let A44 := ident:(A44) in
  let Qsp := ident:(Qsp) in
  let Qgp := ident:(Qgp) in
  let Qtp := ident:(Qtp) in
  let R1 := ident:(R1) in
  let R10 := ident:(R10) in
  let R11 := ident:(R11) in
  let R12 := ident:(R12) in
  let G := ident:(G) in
  let XO := ident:(XO) in
  let OUT := ident:(OUT) in
  let STK := ident:(STK) in
  let sp0 := ident:(sp0) in
  let FP := ident:(FP) in
  let ly := ident:(ly) in
  let S := ident:(S) in
  let W0 := ident:(W0) in
  let mem0 := ident:(mem0) in
  let md0 := ident:(md0) in
  let own := ident:(own) in
  let lyc := ident:(lyc) in
  let Sc := ident:(Sc) in
  let k := ident:(k) in
  let rlo := ident:(rlo) in
  let rhi := ident:(rhi) in
  dec_hc_atom 33%nat (Z_to_bv 64 c0); rewrite unsigned_lit_small in Hc by lia; apply Z.eqb_neq in Hc;
  destruct t as [|b t]; [exfalso; apply Hc; rewrite Hc0def; reflexivity |]; clear Hc;
  dec_run; dec_call_facts;
  eapply SRr_bind;
  [ eapply (dec_strncmp_call rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs);
    [ exact Hat | exact Hat_rt | exact Hpx | exact Hpx_rt | exact HGX | exact HJ | exact HROD
    | exact Hal16 | exact Hwlo | exact Hwhi | exact UN | exact GR | exact Qsp | exact Qgp | exact Qtp
    | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
    | rewrite R10, E11, aarg_reg1; unfold w64; symmetry; apply Z_to_bv_bv_unsigned
    | rewrite R11; reflexivity
    | prreg HS (12%bv : bv 5) R12; exact R12 ]
  | dec_after_call; dec_run; dec_branch;
    [ (* +0x48 taken: the prefix; +0x70 a0 := V_OURS *)
      rewrite (br_eq_atom _ 44 _ A44) in Hc; apply Z.eqb_eq in Hc;
      assert (Hv : has_prefix (b :: t) = true) by (apply Hres; apply bv_eq; rewrite Hc; reflexivity); clear Hc;
      dec_run; dec_finish ltac:(cbn [decide length Nat.eqb negb]; rewrite Hv; reflexivity)
    | (* +0x4c a0 := V_LEAVE_HOST *)
      rewrite (br_eq_atom _ 44 _ A44) in Hc; apply Z.eqb_neq in Hc;
      assert (Hv : has_prefix (b :: t) = false)
        by (apply Bool.not_true_is_false; let Hb := fresh "Hb" in intros Hb; apply Hc; rewrite (proj2 Hres Hb); reflexivity);
      clear Hc; dec_run; dec_finish ltac:(cbn [decide length Nat.eqb negb]; rewrite Hv; reflexivity) ] ].

(* alias[0] is NUL: the kind arm *)
Ltac dec_empty :=
  let Hc := ident:(Hc) in
  let k0 := ident:(k0) in
  let c0 := ident:(c0) in
  let Hc0def := ident:(Hc0def) in
  let t := ident:(t) in
  let b := ident:(b) in
  let kt := ident:(kt) in
  let Hat := ident:(Hat) in
  let Hdec := ident:(Hdec) in
  dec_hc_atom 33%nat (Z_to_bv 64 c0); rewrite unsigned_lit_small in Hc by lia; apply Z.eqb_eq in Hc;
  destruct t as [|b t];
  [ | exfalso; apply (proj2 Hat); left; apply bv_eq; cbn in Hc0def; rewrite <- Hc0def, Hc; reflexivity ]; clear Hc;
  assert (Hdec : decide k0 (Some []) = match k0 with Some kt => if bl_eqb kt S_VLAN then V_LEAVE_VLAN else V_MARK
                                                     | None => V_MARK end) by reflexivity;
  dec_run; dec_kind.

(* alias is NULL: the kind arm *)
Ltac dec_null :=
  let regs := ident:(regs) in
  let Hc := ident:(Hc) in
  let k0 := ident:(k0) in
  let al0 := ident:(al0) in
  let Ha := ident:(Ha) in
  let t := ident:(t) in
  let kt := ident:(kt) in
  let Hdec := ident:(Hdec) in
  dec_hc_atom 11%nat (getr regs 11); rewrite <- aarg_reg1 in Hc; apply Z.eqb_eq in Hc;
  destruct al0 as [t|]; [exfalso; unfold astr_arg in Ha; exact (proj1 Ha Hc) |]; clear Hc;
  assert (Hdec : decide k0 None = match k0 with Some kt => if bl_eqb kt S_VLAN then V_LEAVE_VLAN else V_MARK
                                                | None => V_MARK end) by reflexivity;
  dec_run; dec_kind.

Lemma decide_walk_md : forall rlo rhi, decide_acontract_at SK pa_segs rlo rhi B
  (pa_val A_TEXT + AF_model_decide) (pa_val (A_OBJ 32)) (pa_val (A_OBJ 33)).
Proof.
dec_setup AF_model_decide.
dec_run.
dec_branch.
- dec_null.
- dec_alias. dec_reshape. dec_branch.
  + dec_empty.
  + dec_prefix.
Qed.

Lemma decide_walk_rsd : forall rlo rhi, decide_acontract_at SK pa_segs rlo rhi B
  (pa_val A_TEXT + AF_reac_served_decide) (pa_val (A_OBJ 43)) (pa_val (A_OBJ 44)).
Proof.
dec_setup AF_reac_served_decide.
dec_run.
dec_branch.
- dec_null.
- dec_alias. dec_reshape. dec_branch.
  + dec_empty.
  + dec_prefix.
Qed.

(* The two entries and their literals, as the contract file names them (LinkAddr.v through HV). *)
Theorem model_decide_aproof : model_decide_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
unfold model_decide_acontract.
replace MODEL_DECIDE_A with (pa_val A_TEXT + AF_model_decide) by (rewrite (lv_text HV); reflexivity).
replace LA_MD_PREFIX with (pa_val (A_OBJ 32)) by (rewrite (lv_obj HV 32 ltac:(unfold link_nobj; lia)); reflexivity).
replace LA_MD_VLAN with (pa_val (A_OBJ 33)) by (rewrite (lv_obj HV 33 ltac:(unfold link_nobj; lia)); reflexivity).
exact (decide_walk_md PCAP_RLO PCAP_RHI).
Qed.

Theorem reac_served_decide_aproof : reac_served_decide_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
unfold reac_served_decide_acontract.
replace REAC_SERVED_DECIDE_A with (pa_val A_TEXT + AF_reac_served_decide) by (rewrite (lv_text HV); reflexivity).
replace LA_RSD_PREFIX with (pa_val (A_OBJ 43)) by (rewrite (lv_obj HV 43 ltac:(unfold link_nobj; lia)); reflexivity).
replace LA_RSD_VLAN with (pa_val (A_OBJ 44)) by (rewrite (lv_obj HV 44 ltac:(unfold link_nobj; lia)); reflexivity).
exact (decide_walk_rsd PCAP_RLO PCAP_RHI).
Qed.

End d.
