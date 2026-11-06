(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 1540 of its 1601 lines of code are new or changed and 390 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pj_string.v, with its module names changed; 1107 of its 1191 lines of code are new or changed and 1517 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_caw_emit.v, with its numbers changed; 794 of its 888 lines of code are new or changed and 1097 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_caw_accept.v, with its numbers changed; 43 of its 151 lines of code are new or changed and 780 lines of the source are left out. *)
(* The EMPTY-TEXT arm of the tail of the inlined expected_body of check_as_written (fs.asan A_check_as_written
   0x81590), machine code 0x81738 .. 0x8197c, C source fuzz_state.c:96 with an empty text (strlen = 0, so m = 0
   and the byte at the text pointer is the NUL):

     r = m % 4;
     if ( *text || pad > 2 || r == 1 || (r == 2 && (six[m-1] & 15)) || (r == 3 && (six[m-1] & 3))) n = SIZE_MAX;

   The front of the walk (FSW_caw_front.v) hands the walk over at 0x81738 when strlen gives 0, after it has run
   `mv a3, zero` (0x81730) and `mv a1, zero` (0x81734): that hand-over is cawe_ss738 below (x11 = a1 and
   x13 = a3 are the literal 0).  From there the arm reads the NUL (one shadow check at 0x81740, discharged by
   the SH entry mkSHE 35 0 1), takes `bne a1, 2` to 0x817c8, runs `mv s3, zero` and takes `beqz a3` to 0x8197c
   (`jal __wrap_free` of six) with the answer n = s3 = 0, a0 = six, s2 = want, and touches no memory.
   caw_empty_tail hands the walk over in FSW_caw_accept.v's common 0x8197c state caa_xss, with atom 49 = 0, the
   same exit as caa_accept_m0 (which walks the same code from 0x81724 with m an atom).

   HEADER: no Axiom, no Parameter, no Admitted, no admit, no Abort, no Hypothesis.  This segment calls nothing, so
   it carries no callee contract; every premise is an explicit premise of the lemma, owned by its caller (a Theorem Labs lane).
   The Section carries only the three instance variables of the lane, the allocator symbols B and the goal Q.

   RULE 24 (no function proved): check_as_written - CONFIRM by a Theorem Labs lane 04:15Z (BRIEF-WalkCaw.md, rule-24
   line): no ASan walk of it on any non-lane ref.  fs's RELEASED plain proof lib/Prog/check_as_written.v is a
   TEXT INPUT only, never a proof term of this walk.

   METHOD (measured with the engine over the pinned fs.asan, image sha256
   64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0):
   - the walk is one TOKEN-engine run (FSW_K.fsw_aj_run_to_tokU over YCbn) from 0x81738 to 0x8197c: the shadow
     `lb` of the text byte at 0x81740 becomes a token atom and the following `bnez` is resolved by the engine's
     slow-block pattern; the SH entry mkSHE 35 0 1 covers it, so NO obligation is left and no __asan_report_*
     call is ever reached;
   - a1 and a3 are literals, so every branch (0x8175c, 0x81768, 0x81770, 0x81778, 0x817cc) is decided by the
     engine; no branch split, no m mod 4 reasoning;
   - caa_xss keeps a3 as atom 38 (caa_P keeps atoms < 44): the arm restates the literal a3 = 0 as SOff 38 0
     (caa_setreg) and adds the fact (38, [0, 3145728]) from the premise ew E 38 = 0, then re-keys with
     caa_exit_st; the registers caa_xss re-keys to fresh atoms 44 .. 61 are set from the machine (cawe_mkexit). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP05 YL01 YL02 YL07 YL09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AF0l AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_caw_defs
FSW_caw_tail FSW_caw_emit FSW_caw_accept FSW_caw_front.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the hand-over at 0x81738 is the front's empty-text exit, FSW_caw_front.v cawf_ss738 / cawf_SH738 (taken by
   name, a Theorem Labs lane 05:4xZ): atoms 31 ra (FSW_caw_defs.v caw_regs1: ra is an atom), 33 six, 34 want, 35 the text
   pointer, 37 the byte there (the NUL), 12 / 11 s0 / s1, 32 the shadow base, 42 .. 52 scratch; a1 = a3 = 0
   (`mv a3, zero`, `mv a1, zero`) ---- *)

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable Q : world tfibsegs -> config -> Prop.

(* the entry sp is where the atom fact of the state puts it *)
Lemma cawe_sp_range : forall (W : world tfibsegs) E ms,
  st_ok tfibsegs E cawf_ss738 (restrict (w_H W) ms) ->
  2 ^ 46 <= bv_unsigned (ew E 2) <= 2 ^ 47.
Proof.
intros W E ms (_ & _ & _ & _ & _ & _ & _ & _ & (Hat & _)).
cbn [cawf_ss738 cawf_facts738 ss_facts f_atoms] in Hat.
destruct (atoms_ok_In E _ 2%nat (mkAF (2 ^ 46) (2 ^ 47) 4) Hat
            ltac:(cbn [In]; left; reflexivity)) as [X _].
exact X.
Qed.

(* the register obligations of the re-key: every atom from 44 up is set by the extension list (FSW_caw_accept.v's
   caa_lk is Section-local there, so it is restated here) *)
Ltac cawe_lk EL LD :=
  lazymatch goal with
  | |- ew _ ?j = _ =>
      let jj := eval compute in (Nat.sub j 44) in
      change j with (44 + jj)%nat; rewrite (EL jj ltac:(lia)); unfold LD; cbn [nth]; reflexivity
  end.

(* the whole hand-over at 0x8197c for any state whose register list is not caa_fregs (FSW_caw_accept.v
   caa_mkexit needs x5 .. x7 = atoms 50 .. 52; this arm carries 42 .. 44 there): the env the re-key needs, the
   state, and the answer in atom 49 *)
Lemma cawe_mkexit : forall (W : world tfibsegs) (E E1 : env) (ms0 : machine_state) (ssf : sstate) (nv : Z),
  st_ok tfibsegs E1 ssf (restrict (w_H W) ms0) ->
  ss_pc ssf = 0x8197c ->
  nth_error (ss_mem ssf) 0 = Some caw_stk ->
  reabs_check caa_P ssf caa_xregs (mkFacts caa_xatoms [] []) = true ->
  sr_get (ss_regs ssf) 19%bv = SLit nv ->
  0 <= nv < 2 ^ 64 ->
  (forall nn, (nn < 44)%nat -> ew E1 nn = ew E nn) -> ed E1 = ed E ->
  exists E2, env_agree 44 E E2 /\ st_ok tfibsegs E2 caa_xss (restrict (w_H W) ms0)
             /\ ew E2 49 = Z_to_bv 64 nv.
Proof.
intros W E E1 ms0 ssf nv HS Hpc Hm0 Hchk H19 Hnv Hag Hed.
set (LD := [getr (ms_regs ms0) 11%bv; getr (ms_regs ms0) 12%bv; getr (ms_regs ms0) 14%bv;
            Z_to_bv 64 0; Z_to_bv 64 0; getr (ms_regs ms0) 19%bv;
            getr (ms_regs ms0) 5%bv; getr (ms_regs ms0) 6%bv; getr (ms_regs ms0) 7%bv;
            Z_to_bv 64 0; Z_to_bv 64 0;
            getr (ms_regs ms0) 15%bv; getr (ms_regs ms0) 16%bv; getr (ms_regs ms0) 17%bv;
            getr (ms_regs ms0) 28%bv; getr (ms_regs ms0) 29%bv; getr (ms_regs ms0) 30%bv;
            getr (ms_regs ms0) 31%bv]).
set (E2 := extK E1 44 LD).
assert (EL : forall j, (j < 18)%nat -> ew E2 (44 + j) = nth j LD (Z_to_bv 64 0))
  by (intros j Hj; unfold E2; apply cae_ext_lookup; unfold LD; cbn [length]; lia).
exists E2.
split.
{ split.
  - intros nn Hnn. unfold E2. rewrite (proj1 (env_agree_extK E1 44 LD) nn Hnn). exact (Hag nn Hnn).
  - unfold E2. rewrite (proj2 (env_agree_extK E1 44 LD)). exact Hed. }
split.
{ apply (caa_exit_st W E1 E2 ms0 ssf HS Hpc Hm0 Hchk ltac:(unfold E2; apply env_agree_extK)).
  apply Forall_forall. intros rj Hin. vm_compute in Hin.
  repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; cbn [fst snd]; cawe_lk EL LD. }
change 49%nat with (44 + 5)%nat. rewrite (EL 5%nat ltac:(lia)). unfold LD. cbn [nth].
exact (fsw_reg_lit (w_H W) E1 ssf ms0 19%bv nv HS H19 Hnv).
Qed.

(* ---- the empty-text arm: 0x81738 .. 0x8197c with n = 0 ---- *)
Lemma caw_empty_tail : forall (E : env) (ms : machine_state) (mdc : Model)
    (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
    (Up : list (Z * Z)) (W : world tfibsegs) (kj : Z) (six want Lsix Lwant : Z),
  st_ok tfibsegs E cawf_ss738 (restrict (w_H W) ms) ->
  sh_ok tfibsegs caw_Bx cawf_SH738 E (mrestrict (w_H W) (ms_mem ms)) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms)) mdc kj ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms) mdc ->
  bv_unsigned (ew E 2) = sp0 -> 48 <= STK ->
  ew E 33 = Z_to_bv 64 six -> ew E 34 = Z_to_bv 64 want -> ew E 37 = Z_to_bv 64 0 ->
  ew E 38 = Z_to_bv 64 0 ->
  in_app six Lsix -> in_app want Lwant ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF six Lsix ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF want Lwant ->
  (forall (E2 : env) (ms2 : machine_state) (mdc2 : Model),
     env_agree 44 E E2 ->
     st_ok tfibsegs E2 caa_xss (restrict (w_H W) ms2) ->
     ew E2 49 = Z_to_bv 64 0 ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms2)) mdc2 kj ->
     ARU tfibsegs B lyc Sc Up W (ms_mem ms2) mdc2 ->
     (forall x : word, ~ (sp0 - 48 <= bv_unsigned x < sp0) -> ms_mem ms2 x = ms_mem ms x) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2)) ->
     range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms2))) SHADOW_OFF six Lsix ->
     range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms2))) SHADOW_OFF want Lwant ->
     SRr tfibsegs W (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros E ms mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc Up W kj six want Lsix Lwant
  HS HSH HJ HARU Esp HSTK E33 E34 E37 E38 Happ6 Happw RA6 RAW HCONT.
pose proof ASAN_CEIL_range as [HC1 HC2].
assert (H6lo : 4096 <= six) by (destruct Happ6 as [X _]; exact X).
assert (H6hi : six + Lsix <= CAW_CEIL)
  by (destruct Happ6 as [_ [X|[_ X]]]; unfold kLowShadowBeg, CAW_CEIL in *; lia).
assert (Hwlo : 4096 <= want) by (destruct Happw as [X _]; exact X).
assert (Hwhi : want + Lwant <= CAW_CEIL)
  by (destruct Happw as [_ [X|[_ X]]]; unfold kLowShadowBeg, CAW_CEIL in *; lia).
pose proof (cawe_sp_range W E ms HS) as Hspr. rewrite Esp in Hspr.
(* the fact caa_xss keeps on atom 38 (a3 there) *)
pose proof (cawt_add_atom E _ _ 38%nat (mkAF 0 3145728 0) HS
  ltac:(split; [cbn [af_lo af_hi]; rewrite E38; rewrite unsigned_lit_small by lia; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts cawf_ss738 cawf_facts738 f_atoms f_conds f_alias] in HS1.
clear HS.
fsw_aj_run_to_tokU caw_tbl_ok HS1 HJ HARU HSH caw_Bspan 0x8197c.
{ (* the run writes only the frame window of check_as_written *)
  cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat);
    [ reflexivity | exact Esp | cbn; lia | cbn; lia
    | repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ]. }
{ lazymatch type of HS1 with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
  assert (EQ : forall nn, (nn < 53)%nat -> ew E1 nn = ew E nn)
    by (intros nn Hnn; unfold E1; repeat (rewrite ew_ewset_other by lia); reflexivity).
  assert (KF : forall x : word, ~ (sp0 - 48 <= bv_unsigned x < sp0) -> ms_mem ms0 x = ms_mem ms x).
  { intros x Hx. apply HF. intros (rr & Hin & Hb).
    cbn [ss_mem In] in Hin.
    destruct Hin as [<-|[<-|[]]];
      cbn [caw_stk cawf_txt738 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
      [rewrite Esp in Hb|..]; apply Hx; lia. }
  (* a3 = 0 restated as atom 38, the register caa_xss keeps *)
  lazymatch type of HS1 with
  | st_ok _ _ ?SSF _ =>
      pose proof (caa_setreg E1 SSF (restrict (w_H W) ms0) 13%bv (SOff 38 0) HS1 ltac:(vm_compute; reflexivity)
        ltac:(let x := eval vm_compute in (sr_get (ss_regs SSF) 13%bv) in
              change (sr_get (ss_regs SSF) 13%bv) with x;
              rewrite fsw_SOff0, (EQ 38%nat ltac:(lia)), E38; reflexivity)) as HS2
  end.
  clear HS1.
  destruct (cawe_mkexit W E E1 ms0 _ 0 HS2
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(lia) ltac:(intros nn Hnn; apply EQ; lia) ltac:(unfold E1; reflexivity))
    as (E2 & HAG & HSX & H49).
  apply (HCONT E2 ms0 _); [exact HAG | exact HSX | exact H49 | exact HJ | exact HARU | exact KF | exact HG | |].
  - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (sp0 - 48) sp0 RA6 KF);
      [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia].
  - apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (sp0 - 48) sp0 RAW KF);
      [lia | right; unfold kHighMemBeg in *; lia | lia | unfold CAW_CEIL in *; lia]. }
Qed.

End W.
