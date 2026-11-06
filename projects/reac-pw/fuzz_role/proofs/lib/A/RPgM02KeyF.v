(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the call in the middle of a walk: the run
   to the jal, the callee's contract through SRr_bind, a fresh entry state at the return pc) for the common value
   tail of reac-pw/fuzz_role's image-A segment M02 (0x823e0 .. 0x823f8: the role's range test, check_role, the jump
   to T). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyV.v, with its module names and addresses changed; 507 of its 578 lines of code are new or changed and 177 lines of the source are left out. *)
(* reac-pw/fuzz_role, image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, the same loaded bytes): THE FLOAT VALUE ARM of
   the key match of segment M02's match half, 0x82398 .. 0x823e0 (and MAL 0x823fc), for lib/A/RPgM02Key.v.
   Proves no function (kind: segment lemma): rl_m02_key_float.

   THE CODE (capstone over the pinned file):
     0x82398 addi a1,a0,4; 0x8239c .. 0x823a8 the shadow check of a1; 0x823ac lw a1,0(a1) (= ent[v].size);
     0x823b0 li a2,4; 0x823b4 bltu a1,a2 -> MAL 0x823fc;
     0x823b8 addi a0,a0,8; 0x823bc .. 0x823c8 the shadow check of a0; 0x823cc flw fa0,0(a0) (the body word);
     0x823d0 addi a0,s1,0x118; 0x823d4 jal pod_nearest 0x82ccc (ra = 0x823d8);
     0x823d8 beqz a0 -> MAL 0x823fc; 0x823dc ld a2,0x118(s1); 0x823e0 is the value tail (rl_m02_key_tail).

   THE WALK, in three runs of the engine and two steps it has no rule for:
   - m2f_walk1: from 0x82398, the value entry's size and body word as the one region (atoms 32 and 33) and the
     shadow entry m2k_SH over [&ent[v], &ent[v] + 16), so both checks read shadow 0. The engine stops at the size
     test; on the taken side a run reaches MAL; on the other side the run stops at the `flw` (no rule), which
     m2f_flw steps by YK0o.fp_step_flw: the four bytes of the body word are YN2e.le_list b 4, and the float state
     becomes m2f_fxA fx b (f10 = the NaN-boxed b, rl_fxk [10; 13; 14; 15] kept by m2k_fxk_set).
   - m2f_walk2: from 0x823d0 at that float state, one run to the `jal`, then pod_nearest through its PROVED
     contract RPgNear.rl_pod_nearest_A_of (RPgNearW.pod_nearest_A_holds NearSFClose.near_sf_facts_ok), whose out
     cell R + 0x118 is in the caller's stack window, 8-aligned, and marked usable (m2f_ra_out: the hi_rz range of
     the segment's start, carried by rs_core); its post comes back through m2_core_call.
   - m2f_walk3: from 0x823d8 with a0 as the literal pod_nearest returned: on None the engine takes the `beqz` to
     MAL; on Some r the real frame's cell R + 0x118 (holding r mod 2^64) is the one region and a run reaches
     0x823e0 with a2 = r mod 2^64.
   The MAL exit (m2f_exit_mal) and the state at 0x823e0 (m2f_cut) are RPgSeg's cuts rebuilt from the cut at
   0x82398 by RPgM02KeyBase's m2k_chk_kept / m2k_at_kept: every byte outside m2k_wz (the callees' stack and
   R + 0xd8 .. R + 0x120) is as at 0x82398, and every callee-saved register too. The answer is expect_value of
   the entry (m2k_expect_none / m2k_expect_float, then m2k_flag_small / m2k_flag_big).

   SECTION HYPOTHESES of rl_m02_key_float: MTL : ameter_laws MT, LAWS : AR_laws rsegs B, HGOT : as_got_shadow B =
   0x9a830 and HSC : as_shadow_cell B = 0xa33f8 (the last two for the pod_nearest lift). Nothing else is assumed. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o YN2e.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSeg RPgStrcmp RPgMem RPgCheck RPgCheckStr RPgScanF RPgM02Base.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgM02KeyBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgNear RPgNearW.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require NearSFClose.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the float state after 0x823cc flw fa0,0(a0): f10 holds the NaN-boxed binary32 b, the rest is as in f *)
Definition m2f_fxA (f : YK11.FPState) (b : Z) : YK11.FPState :=
YK11.mkFP (bvmap_set (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b)) (@fp_regs f)) (@fp_csr f).

(* ======================================= the `flw` ======================================= *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* 0x823cc flw fa0,0(a0) with a0 = a and the 4 bytes at a holding b; the walk goes on at 0x823d0 *)
Lemma m2f_flw : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) a b,
getr regs (Z_to_bv 5 10) = Z_to_bv 64 a -> 0 <= a -> a + 4 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) mem) a 4 b -> 0 <= b < 2 ^ 32 ->
(forall X, SRr rsegs W (@cfg_at (m2f_fxA fx b) rsegs 0x823d0 regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x823cc) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q a b H10 Ha0 Ha1 Hval Hb HK.
pose proof (m2_entry (fx := m2f_fxA fx b) 0x823d0 [] [] (mkFacts [] [] []) W regs [] mem (Forall_nil _) eq_refl
  (Forall_nil _) I ltac:(repeat split)) as HS'.
assert (Hrd : rdn rsegs (mrestrict (w_H W) mem) (Z_to_bv 64 a) 4 = Some (YN2e.le_list b 4))
by (apply YN2e.rdn_cell; intros k Hk; exact (Hval k Hk)).
assert (Hw : bv_extract 0 32 (le_bytes_to_word (YN2e.le_list b 4)) = Z_to_bv 32 b).
{ rewrite le_bytes_to_word_Z, YN2e.bytes_le_to_Z_le_list.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small b (2 ^ 32)) by lia.
  apply bv_eq. rewrite bv_extract_unsigned, unsigned_lit_small by lia. rewrite Z_to_bv_unsigned.
  try (f_equal; apply Z.shiftr_0_r). }
refine (@SRr_msteps_st rsegs (m2f_fxA fx b) m2_wx W _ _ (@mkst fx regs (Z_to_bv 64 0x823cc) mem (seg_rom rsegs))
  _ md Q _ HS' _).
- rewrite !restrict_mkst_fx. apply msteps_one; [reflexivity|].
  rewrite (YK0o.fp_step_flw fx rsegs regs (Z_to_bv 64 0x823cc) (mrestrict (w_H W) mem) (seg_rom rsegs)
    (Z_to_bv 32 0x52507) (Z_to_bv 5 10) (Z_to_bv 5 10) (Z_to_bv 12 0) (Z_to_bv 64 a) (YN2e.le_list b 4));
  [ | vm_refl_bv | vm_compute; reflexivity | vm_refl_bv
    | rewrite H10; replace (bv_signed (Z_to_bv 12 0)) with 0 by reflexivity; apply v_addi_0
    | exact Hrd ].
  rewrite Hw. reflexivity.
- intros ms' mat' HS2 Hlo Hhi Hreg.
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms' HS2 eq_refl).
  assert (Hm : ms_mem ms' = mem).
  { apply functional_extensionality. intros x. destruct (w_H W x) eqn:Hx.
    - rewrite (Hhi x Hx). reflexivity.
    - rewrite (Hlo x Hx). cbn [ms_mem restrict mkst]. unfold mrestrict. rewrite Hx. reflexivity. }
  rewrite Hm, Hreg. exact (HK mat').
Qed.
End s.

(* ======================================= the three runs ======================================= *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HGOT : as_got_shadow B = 0x9a830.
Hypothesis HSC : as_shadow_cell B = 0xa33f8.

(* 0x82398 .. 0x823cc: the size test, then the `flw` *)
Lemma m2f_walk1 : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2
  a0v sz bd,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)) -> getr regs2 (Z_to_bv 5 23) = w64 SHADOW_OFF ->
getr regs2 (Z_to_bv 5 10) = w64 a0v -> 4096 <= a0v -> a0v + 16 <= alloc_ceiling ->
(a0v + 16 <= kLowShadowBeg \/ kHighMemBeg <= a0v) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF a0v 16 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 4) 4 sz -> 0 <= sz < 2 ^ 31 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 8) 4 bd -> 0 <= bd < 2 ^ 32 ->
(sz < 4 -> forall ly3 S3 W3 regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (@cfg_at fx rsegs 0x823fc regs3 mem3 md3) POST) ->
(4 <= sz -> forall ly3 S3 W3 regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (@cfg_at (m2f_fxA fx bd) rsegs 0x823d0 regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs 0x82398 regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST ly2 S2 W2 regs2 mem2 md2 a0v sz bd Hpre Hcore H9 H23 H10 Ha1 Ha2 Happ Hra Hsz Hsz' Hbd Hbd'
  KMAL KF.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof (@ASAN_CEIL_range rc) as (Cc & _). unfold ASAN_CEIL in Cc.
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
assert (E9 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bd]) 9 = Z_to_bv 64 (e_R (x_e rsegs cx)))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
assert (E23 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bd]) 23 = Z_to_bv 64 SHADOW_OFF)
by (rewrite (ew_Ereg_nat regs2 _ 23 23%bv eq_refl); exact H23).
assert (E10 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bd]) 10 = Z_to_bv 64 a0v)
by (rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bd]) 32 = Z_to_bv 64 sz)
by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bd]) 33 = Z_to_bv 64 bd)
by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
pose proof (m2_entry (fx := fx) 0x82398 []
  [YP09.mkRegion (Some 10%nat) 4 12 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0))]]
  m2k_facts10 W2 regs2 [Z_to_bv 64 sz; Z_to_bv 64 bd] mem2 (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (rm_ro_region rsegs _ (w_H W2) mem2 10 a0v 4 12);
  [ rewrite E10; apply unsigned_lit_small; lia | lia | lia |
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    [ apply (chunk_ok_val rsegs _ _ a0v 4 4 (SOff 32 0) sz);
      [ apply m2k_denot_of_U; apply U_atom; [exact E32 | lia] | cbn; lia | cbn; lia | exact Hsz ]
    | apply (chunk_ok_val rsegs _ _ a0v 8 4 (SOff 33 0) bd);
      [ apply m2k_denot_of_U; apply U_atom; [exact E33 | lia] | exact Hbd' | cbn; lia | exact Hbd ] ] ])).
specialize (HS ltac:(cbn; tauto)).
specialize (HS (m2k_facts10_ok (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bd]) (e_R (x_e rsegs cx)) a0v
  ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
  ltac:(rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
  ltac:(rewrite E10; apply unsigned_lit_small; lia) ltac:(lia))).
assert (SHOK : sh_ok rsegs M2_Bx m2k_SH (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bd]) (mrestrict (w_H W2) mem2)).
{ apply (m2k_sh_ok W2 mem2 _ a0v); [| | exact Hra | exact Happ].
  - unfold M2_Bx. apply U_atom; [exact E23 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E10 | lia]. }
remember (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bd]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bd]) E) by (subst E; apply env_agree_refl).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 0x82398) with (Z_to_bv 64 0x82398).
(* 0x82398 .. 0x823b0, stop at 0x823b4 bltu size,4 *)
m2_run m2_awr. ck_keep kwr_stk.
m2_branch Hb.
all: rewrite branch_ltu_U, (m2k_U_sext32 E 32 sz E32 ltac:(lia)), U_lit, (m2k_sx_id sz Hsz') in Hb by lia.
- (* taken: the size is below 4, to MAL *)
  assert (Hlt : sz < 4) by (apply Z.ltb_lt; exact Hb).
  m2_run_to m2_awr 0x823fc. ck_keep kwr_stk.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (Hpr : aregs_preserved regs2 (ms_regs ms))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with 0x823fc by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KMAL Hlt ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ intros r Hr; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | kio
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x)) ]
  end.
- (* not taken: the body word, then the `flw` *)
  assert (Hge : 4 <= sz) by (apply Z.ltb_ge; exact Hb).
  m2_run m2_awr. ck_keep kwr_stk.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msT end.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H msT), HAE : env_agree 32 _ ?E |- _ =>
    assert (G10 : getr (ms_regs msT) (Z_to_bv 5 10) = Z_to_bv 64 (a0v + 8))
    by (rewrite (st_ok_restrict_reg rsegs H E ss msT (Z_to_bv 5 10) HS);
        replace (sr_get (ss_regs ss) (Z_to_bv 5 10)) with (SOff 10 8) by (vm_compute; reflexivity);
        apply m2k_denot_of_U; apply U_atom_off; [exact E10 | lia | lia]);
    assert (Hpr : aregs_preserved regs2 (ms_regs msT))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss msT HS eq_refl);
    replace (ss_pc ss) with 0x823cc by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msT) ?mdT _ |- _ =>
  apply (m2f_flw W2 (ms_regs msT) (ms_mem msT) mdT POST (a0v + 8) bd G10 ltac:(lia) ltac:(lia));
  [ apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 (ms_mem msT) (a0v + 8) 4 bd); [|exact Hbd];
    intros k Hk; cbn in Hk; exact (KE (a0v + 8 + k) ltac:(lia) (fun x => x))
  | exact Hbd'
  | intros X; apply (KF Hge ly2 S2 W2 (ms_regs msT) (ms_mem msT) (with_vm_backing (m_vm_lazy mdT) X mdT));
    [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ Hcore
        (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HJ));
      [ intros r Hr; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | kio
      | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
    | exact Hpr
    | intros a Ha; exact (KE a Ha (fun x => x)) ] ]
  end.
Qed.

(* the out cell R + 0x118 of pod_nearest: its 8 bytes are marked usable at every state of the segment (hi_rz at
   the segment's start; the shadow bytes lie in the high shadow, below R - T_SEG_STK and apart from rs_E2) *)
Lemma m2f_ra_out : forall (cx : rs_scx rsegs) ly4 S4 W4 regs4 mem4 md4,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly4 S4 W4 regs4 mem4 md4 ->
range_addressable (aview rsegs (w_H W4) mem4) SHADOW_OFF (e_R (x_e rsegs cx) + 0x118) 8.
Proof using LAWS.
intros cx ly4 S4 W4 regs4 mem4 md4 Hpre Hpod Hcore.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & _).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & Fapp & _).
pose proof asan_consts as (C1 & _).
pose proof Hpre as Hp. unfold rs_pre, rl_seg_pre in Hp.
destruct Hp as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrz & _).
cbn [hi_rz role_himg_A] in Hrz. rewrite Forall_cons_iff in Hrz. destruct Hrz as (Hrz & _). cbn [fst snd] in Hrz.
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & Papp & _).
assert (Hreq : e_len (x_e rsegs cx) <= req_size (e_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (e_len (x_e rsegs cx)) 0); lia).
destruct Hcore as (_ & _ & _ & _ & _ & _ & HK).
intros x Hx. destruct (Hrz x ltac:(lia)) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite <- Hsv.
assert (L1 : 2 ^ 43 <= x / 8) by (apply Z.div_le_lower_bound; lia).
assert (L2 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (e_F (x_e rsegs cx)) 8 ltac:(lia)) as DF.
pose proof (Z.mod_pos_bound (e_F (x_e rsegs cx)) 8 ltac:(lia)) as MF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Papp.
apply HK.
- unfold shadow_of_addr, SHADOW_OFF. lia.
- rewrite HR. unfold shadow_of_addr, SHADOW_OFF, T_SEG_STK, ASTACK. lia.
- unfold rs_E2, rl_inw. cbn [hi_w2 role_himg_A]. intros [Hw|Hw].
  + rewrite !Exists_cons, Exists_nil in Hw. cbn [rl_xv fst snd] in Hw.
    unfold shadow_of_addr, shadow_addr, SHADOW_OFF, T_SEG_STK, ASTACK in *.
    destruct Hw as [Hw|[Hw|[Hw|[Hw|[]]]]]; lia.
  + unfold shadow_of_addr, SHADOW_OFF in Hw. lia.
Qed.

(* 0x823d0 .. 0x823d4 at the float state after the `flw`, then pod_nearest *)
Lemma m2f_walk2 : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2 b,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)) ->
0 <= b < 2 ^ 32 -> Sem.reg_get (@fp_regs fx) (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b) ->
YK0o.frm_zero (@fp_csr fx) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_R (x_e rsegs cx) + 0x118) 8 ->
rom_view rsegs W2 mem2 ->
(forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3,
  rl_fxk [15] fx fx3 ->
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  getr regs3 (Z_to_bv 5 10) = w64 (rl_near_rc (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX)) ->
  match Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX with
  | Some r => val_mem rsegs (mrestrict (w_H W3) mem3) (e_R (x_e rsegs cx) + 0x118) 8 (r mod 2 ^ 64)
  | None => True
  end ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_nearest_STK <= a < e_R (x_e rsegs cx)) ->
   ~ (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
      e_R (x_e rsegs cx) + 0x118 <= a < e_R (x_e rsegs cx) + 0x118 + 8) ->
   aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (@cfg_at fx3 rsegs 0x823d8 regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs 0x823d0 regs2 mem2 md2) POST.
Proof using MTL LAWS HGOT HSC.
intros cx POST ly2 S2 W2 regs2 mem2 md2 b Hpre Hcore H9 Hb HF10 Hfrm Hra Hrom KN.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
assert (Hsp : spZ regs2 = e_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
assert (E9 : ew (Ereg regs2 []) 9 = Z_to_bv 64 (e_R (x_e rsegs cx)))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
pose proof (m2_entry (fx := fx) 0x823d0 [] [] (mkFacts [] [] []) W2 regs2 [] mem2 (Forall_nil _) eq_refl
  (Forall_nil _) I ltac:(repeat split)) as HS.
remember (Ereg regs2 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 0x823d0) with (Z_to_bv 64 0x823d0).
(* 0x823d0 addi a0,s1,0x118; 0x823d4 jal pod_nearest: stop at 0x82ccc *)
m2_run m2_awr. ck_keep kwr_stk.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msT end.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H msT), HAE : env_agree 32 _ ?E |- _ =>
  assert (G10 : getr (ms_regs msT) (Z_to_bv 5 10) = w64 (e_R (x_e rsegs cx) + 0x118))
  by (rewrite (st_ok_restrict_reg rsegs H E ss msT (Z_to_bv 5 10) HS);
      replace (sr_get (ss_regs ss) (Z_to_bv 5 10)) with (SOff 9 0x118) by (vm_compute; reflexivity);
      apply m2k_denot_of_U; apply U_atom_off; [exact E9 | lia | lia]);
  assert (G1 : getr (ms_regs msT) 1 = w64 0x823d8)
  by (rewrite (st_ok_restrict_reg rsegs H E ss msT 1%bv HS);
      replace (sr_get (ss_regs ss) 1%bv) with (SLit 0x823d8) by (vm_compute; reflexivity);
      reflexivity);
  assert (Hpr : aregs_preserved regs2 (ms_regs msT))
  by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
  rewrite (st_ok_restrict_mkst rsegs H E ss msT HS eq_refl);
  replace (ss_pc ss) with RPgNear.NC.A_POD_NEAREST by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs msT) = e_R (x_e rsegs cx)) by (rewrite (m2k_sp_pres _ _ Hpr); exact Hsp).
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msT) ?mdT _ |- _ =>
assert (HcoreT : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT)
by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT Hcore HJ);
    [ intros r Hr; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | kio
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ])
end.
assert (HEc : forall a, (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
  e_R (x_e rsegs cx) + 0x118 <= a < e_R (x_e rsegs cx) + 0x118 + 8) -> rs_E2 rsegs cx a).
{ intros a (_ & Ha). left. unfold rl_inw. cbn [hi_w2 role_himg_A].
  apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd.
  cbn [rl_xv fst snd]. lia. }
eapply SRr_bind.
{ apply (RPgNear.rl_pod_nearest_A_of (fx := fx) B MT MTL LAWS HGOT HSC
    (RPgNearW.pod_nearest_A_holds NearSFClose.near_sf_facts_ok)
    (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem msT) _ (x_k rsegs cx) (ms_regs msT)
    (e_R (x_e rsegs cx) + 0x118) b).
  - apply (m2_pre_call B MT cx _ _ _ _ _ _ _ T_nearest_STK Hpre HcoreT);
    [ rewrite G1; vm_compute; reflexivity
    | unfold raZ; rewrite G1; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_nearest_STK, T_SEG_STK, ASTACK; lia ].
  - exact G10.
  - exact Hb.
  - exact HF10.
  - unfold rl_wcell. rewrite HspT. unfold T_SEG_STK, ASTACK in *. split; [left; split; lia | left; lia].
  - pose proof (Z.div_mod (e_R (x_e rsegs cx)) 16 ltac:(lia)) as D. rewrite Hal in D.
    replace (e_R (x_e rsegs cx) + 0x118) with ((2 * (e_R (x_e rsegs cx) / 16) + 35) * 8) by lia.
    apply Z_mod_mult.
  - apply (rm_ra_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem msT) _ _ _ Hra). intros x Hx.
    assert (0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    apply KE; [unfold shadow_of_addr, SHADOW_OFF; lia | intros []].
  - apply (rm_rom_kept rsegs W2 W2 mem2 (ms_mem msT) Hrom). intros a (sg & Hin & _ & Hr).
    pose proof (Hsegs a (ex_intro _ sg (conj Hin Hr))) as Hlow. unfold kLowMemEnd in Hlow.
    apply KE; [lia | intros []].
  - exact Hfrm. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun x => Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
  e_R (x_e rsegs cx) + 0x118 <= x < e_R (x_e rsegs cx) + 0x118 + 8) T_nearest_STK ly2 S2 W2 (ms_regs msT)
  (ms_mem msT) _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK; lia) HEc Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & Hrc3).
subst c3. rewrite G1. destruct Hrc3 as (H10' & Hval').
apply (KN fx3 ly3 S3 W3 regs3 mem3 md3 Hfx3 Hcore3 (aregs_preserved_trans _ _ _ Hpr Hpres3) H10' Hval').
intros a Ha Hs Hn. rewrite (Hkept3 a Ha Hs Hn). exact (KE a Ha (fun x => x)).
Qed.

(* 0x823d8 beqz a0 -> MAL; 0x823dc ld a2,0x118(s1); to 0x823e0 *)
Lemma m2f_walk3 : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2
  (o : option Z),
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)) ->
getr regs2 (Z_to_bv 5 10) = w64 (rl_near_rc o) ->
match o with
| Some r => val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x118) 8 (r mod 2 ^ 64)
| None => True
end ->
(o = None -> forall ly3 S3 W3 regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (@cfg_at fx rsegs 0x823fc regs3 mem3 md3) POST) ->
(forall r, o = Some r -> forall ly3 S3 W3 regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  getr regs3 (Z_to_bv 5 12) = w64 (r mod 2 ^ 64) ->
  SRr rsegs W3 (@cfg_at fx rsegs 0x823e0 regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs 0x823d8 regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST ly2 S2 W2 regs2 mem2 md2 o Hpre Hcore H9 H10 Hval KN KS.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
pose proof (proj1 Hcore) as HJ.
destruct o as [r|].
- (* Some r: the `beqz` is not taken; a2 = the 8 bytes at R + 0x118 *)
  assert (Hr64 : 0 <= r mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (E9 : ew (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 64)]) 9 = Z_to_bv 64 (e_R (x_e rsegs cx)))
  by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
  assert (E32 : ew (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 64)]) 32 = Z_to_bv 64 (r mod 2 ^ 64))
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  pose proof (m2_entry (fx := fx) 0x823d8 [((10%bv : bv 5), SLit 1)]
    [m2_frame 0x118 0x120 0 0 [YP09.mkChunk 0x118 (CVal 8 (SOff 32 0))]] m2_facts W2 regs2
    [Z_to_bv 64 (r mod 2 ^ 64)] mem2) as HS.
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
    [ intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
    | rewrite ck_lit; symmetry; exact H10 ]) eq_refl).
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; unfold m2_frame;
    apply (rm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e rsegs cx)) 0x118 0x120);
    [ rewrite E9; apply unsigned_lit_small; lia | lia | lia |
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val rsegs _ _ (e_R (x_e rsegs cx)) 0x118 8 (SOff 32 0) (r mod 2 ^ 64));
      [ apply m2k_denot_of_U; apply U_atom; [exact E32 | exact Hr64] | exact Hr64 | cbn; lia | exact Hval ] ])).
  specialize (HS ltac:(cbn; tauto)
    (m2_facts_ok (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 64)]) (e_R (x_e rsegs cx))
      ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal)).
  remember (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 64)]) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 64)]) E) by (subst E; apply env_agree_refl).
  assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
  unfold cfg_at. change (w64 0x823d8) with (Z_to_bv 64 0x823d8).
  m2_run_to m2_awr 0x823e0. ck_keep kwr_stk.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (G12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (r mod 2 ^ 64))
    by (rewrite (st_ok_restrict_reg rsegs H E ss ms (Z_to_bv 5 12) HS);
        replace (sr_get (ss_regs ss) (Z_to_bv 5 12)) with (SOff 32 0) by (vm_compute; reflexivity);
        apply m2k_denot_of_U; apply U_atom; [exact E32 | exact Hr64]);
    assert (Hpr : aregs_preserved regs2 (ms_regs ms))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with 0x823e0 by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KS r eq_refl ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ intros q Hq; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | kio
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x))
  | exact G12 ]
  end.
- (* None: the `beqz` is taken, to MAL *)
  pose proof (m2_entry (fx := fx) 0x823d8 [((10%bv : bv 5), SLit 0)] [] (mkFacts [] [] []) W2 regs2 [] mem2) as HS.
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
    [ intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
    | rewrite ck_lit; symmetry; exact H10 ]) eq_refl (Forall_nil _) I ltac:(repeat split)).
  remember (Ereg regs2 []) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
  assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
  unfold cfg_at. change (w64 0x823d8) with (Z_to_bv 64 0x823d8).
  m2_run_to m2_awr 0x823fc. ck_keep kwr_stk.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (Hpr : aregs_preserved regs2 (ms_regs ms))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with 0x823fc by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KN eq_refl ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ intros q Hq; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | kio
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x)) ]
  end.
Qed.
End k.

(* ======================================= the arm ======================================= *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HGOT : as_got_shadow B = 0x9a830.
Hypothesis HSC : as_shadow_cell B = 0xa33f8.

(* the cut at 0x82398 (without a0), carried to a state of the arm: only m2k_wz is written, every callee-saved
   register is kept, the float state is fx3 *)
Lemma m2f_cut : forall (cx : rs_scx rsegs) rec (fx2 fx3 : YK11.FPState)
  ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx ->
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_role_at rsegs cx rec W2 mem2 -> Z.of_nat (length (Layout.pp_bytes rec)) = Layout.PP_SIZE ->
rs_at_cx rsegs cx W2 mem2 regs2
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 25, e_F (x_e rsegs cx));
                         (LReg 27, e_pp (x_e rsegs cx))]) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
rl_fxk [10; 13; 14; 15] fx fx3 ->
(forall a, ~ m2k_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
@rs_chk_base fx rc SK rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 /\ rs_role_at rsegs cx rec W3 mem3 /\
rs_at_cx rsegs cx W3 mem3 regs3
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 25, e_F (x_e rsegs cx));
                         (LReg 27, e_pp (x_e rsegs cx))]).
Proof using LAWS.
intros cx rec fx2 fx3 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre HCB HRA Hppl HAT Hcore3 Hpr Hfxk3 HK.
destruct (m2k_chk_kept (fx := fx) B MT LAWS cx rec fx2 fx3 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
  Hpre HCB HRA Hppl Hcore3 Hfxk3 HK) as (HCB3 & HRA3).
split; [exact HCB3|]. split; [exact HRA3|].
pose proof (m2_stack B cx Hpre) as (_ & _ & Hrsz & _ & _ & H46 & H47 & _).
apply (m2k_at_kept cx W2 W3 mem2 mem3 regs2 regs3 (m2k_wz cx) _ (fun a _ Hw => HK a Hw) Hpr); [|exact HAT].
unfold rs_L_chk. cbn [app].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; try (unfold acallee_saved; lia).
all: intros i Hi; cbn [rl_xv]; unfold m2k_wz, T_SEG_STK, ASTACK; split; lia.
Qed.

(* the MAL exit of the arm, from a state the cut at 0x82398 carries to, when the answer is (None, -1) *)
Lemma m2f_exit_mal : forall (cx : rs_scx rsegs) POST rec (fx2 fx3 : YK11.FPState)
  ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx -> @rs_from_MAL fx rc SK rsegs B MT cx POST ->
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_role_at rsegs cx rec W2 mem2 -> Z.of_nat (length (Layout.pp_bytes rec)) = Layout.PP_SIZE ->
rs_at_cx rsegs cx W2 mem2 regs2
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 25, e_F (x_e rsegs cx));
                         (LReg 27, e_pp (x_e rsegs cx))]) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
rl_fxk [10; 13; 14; 15] fx fx3 ->
(forall a, ~ m2k_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_PA rsegs cx rec = (None, -1) ->
SRr rsegs W3 (@cfg_at fx3 rsegs 0x823fc regs3 mem3 md3) POST.
Proof using LAWS.
intros cx POST rec fx2 fx3 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre HMAL HCB HRA Hppl HAT Hcore3 Hpr
  Hfxk3 HK HPA.
destruct (m2f_cut cx rec fx2 fx3 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre HCB HRA Hppl HAT Hcore3
  Hpr Hfxk3 HK) as (HCB3 & HRA3 & HAT3).
rewrite HPA in HAT3. cbn [snd] in HAT3.
apply (m2k_mal (fx := fx) B MT cx POST rec fx3 ly3 S3 W3 regs3 mem3 md3 HMAL HCB3 HRA3 HAT3);
rewrite HPA; reflexivity.
Qed.

Lemma rl_m02_key_float : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop)
  (rec : Model.pod_rec) (ent : Model.ent) (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 (a0v : Z),
@rs_from_MAL fx rc SK rsegs B MT cx POST ->
(* the continuation of the value tail at 0x823e0, in the shape my file hands you *)
(forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3 (v : Z),
   @rs_chk_base fx rc SK rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
   rs_role_at rsegs cx rec W3 mem3 ->
   rs_at_cx rsegs cx W3 mem3 regs3
     (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 25, e_F (x_e rsegs cx));
                            (LReg 27, e_pp (x_e rsegs cx))]) ->
   getr regs3 (Z_to_bv 5 12) = w64 v -> 0 <= v < 2 ^ 64 ->
   (v < 2 -> snd (rs_PA rsegs cx rec) = 1 /\ rs_rcell (fst (rs_PA rsegs cx rec)) = v) ->
   (2 <= v -> fst (rs_PA rsegs cx rec) = None /\ snd (rs_PA rsegs cx rec) = -1) ->
   SRr rsegs W3 (@cfg_at fx3 rsegs 0x823e0 regs3 mem3 md3) POST) ->
rs_pre rsegs B cx ->
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_role_at rsegs cx rec W2 mem2 ->
Z.of_nat (length (Layout.pp_bytes rec)) = Layout.PP_SIZE ->
rs_at_cx rsegs cx W2 mem2 regs2
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 10, a0v);
                         (LReg 25, e_F (x_e rsegs cx)); (LReg 27, e_pp (x_e rsegs cx))]) ->
Model.ent_wf ent -> Model.e_type ent = Model.POD_FLOAT ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 4) 4 (Model.e_size ent) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 8) 4 (Cursor.rd32 (Model.e_body ent)) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF a0v 16 ->
4096 <= a0v -> a0v + 16 <= alloc_ceiling ->
(a0v + 16 <= kLowShadowBeg \/ kHighMemBeg <= a0v) ->
rs_E0 rec = Role.expect_value ent ->
snd (rs_PA rsegs cx rec) = snd (rs_E0 rec) -> fst (rs_PA rsegs cx rec) = fst (rs_E0 rec) ->
SRr rsegs W2 (@cfg_at fx2 rsegs 0x82398 regs2 mem2 md2) POST.
Proof using MTL LAWS HGOT HSC.
intros cx POST rec ent fx2 ly2 S2 W2 regs2 mem2 md2 a0v HMAL HV Hpre Hbase Hrole Hlen Hat Hwf Hty Hsz Hbd Hra
  Ha1 Ha2 Happ HE0 HPs HPf.
pose proof Hbase as (Hcore & Hfxk & _ & Hrom & _ & _ & _ & _ & Hpod & _).
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & _).
pose proof Hwf as (Hwt & Hwb & Hws).
pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk in Hat'. rewrite Forall_app, !Forall_cons_iff in Hat'.
destruct Hat' as ((A8 & A9 & A19 & A23 & A18 & A22 & AC8 & AC30 & _) & A24 & A10 & A25 & A27 & _).
cbn [rl_at rl_xv fst snd] in A9, A23, A10.
assert (HatL : rs_at_cx rsegs cx W2 mem2 regs2
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 25, e_F (x_e rsegs cx));
                         (LReg 27, e_pp (x_e rsegs cx))])).
{ unfold rs_at_cx, rs_at in Hat |- *. rewrite Forall_app in Hat |- *. destruct Hat as (HL1 & HL2).
  split; [exact HL1|]. rewrite !Forall_cons_iff in HL2. destruct HL2 as (X24 & _ & X25 & X27 & _).
  apply Forall_cons; [exact X24|]. apply Forall_cons; [exact X25|]. apply Forall_cons; [exact X27 | apply Forall_nil]. }
assert (HPA : rs_PA rsegs cx rec = Role.expect_value ent).
{ rewrite <- HE0, (surjective_pairing (rs_PA rsegs cx rec)), HPf, HPs. symmetry. apply surjective_pairing. }
assert (HwzK : forall a, ~ m2k_wz cx a -> 0 <= a < 2 ^ 64) by (intros a Hw; unfold m2k_wz in Hw; lia).
apply (m2f_walk1 (fx := fx2) B MT MTL LAWS cx POST ly2 S2 W2 regs2 mem2 md2 a0v (Model.e_size ent)
  (Cursor.rd32 (Model.e_body ent)) Hpre Hcore A9 A23 A10 Ha1 Ha2 Happ Hra Hsz ltac:(lia) Hbd (m2k_rd32_range _)).
- (* the size is below 4: MAL *)
  intros Hlt ly3 S3 W3 regs3 mem3 md3 Hcore3 Hpr3 K3.
  apply (m2f_exit_mal cx POST rec fx2 fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre HMAL Hbase Hrole
    Hlen HatL Hcore3 Hpr3 Hfxk).
  + intros a Hw. exact (K3 a (HwzK a Hw)).
  + rewrite HPA. apply m2k_expect_none; [exact Hwf | right; exact Hlt].
- (* the body word in fa0, then pod_nearest *)
  intros Hge ly3 S3 W3 regs3 mem3 md3 Hcore3 Hpr3 K3.
  assert (HfxA : rl_fxk [10; 13; 14; 15] fx (m2f_fxA fx2 (Cursor.rd32 (Model.e_body ent))))
  by (apply m2k_fxk_set; [left; reflexivity | exact Hfxk]).
  assert (Hrom3 : rom_view rsegs W3 mem3).
  { apply (rm_rom_kept rsegs W2 W3 mem2 mem3 Hrom). intros a (sg & Hin & _ & Hr).
    pose proof (m2_segs_low a (ex_intro _ sg (conj Hin Hr))) as Hlow. unfold kLowMemEnd in Hlow.
    apply K3. lia. }
  apply (m2f_walk2 (fx := m2f_fxA fx2 (Cursor.rd32 (Model.e_body ent))) B MT MTL LAWS HGOT HSC cx POST
    ly3 S3 W3 regs3 mem3 md3 (Cursor.rd32 (Model.e_body ent)) Hpre Hcore3
    ltac:(rewrite (Hpr3 9 ltac:(unfold acallee_saved; lia)); exact A9) (m2k_rd32_range _)
    (regupd_same (@fp_regs fx2) (Z_to_bv 5 10) (nan_box (Z_to_bv 32 (Cursor.rd32 (Model.e_body ent)))))
    (proj2 Hfxk) (m2f_ra_out B MT LAWS cx ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3) Hrom3).
  intros fx3 ly4 S4 W4 regs4 mem4 md4 Hfx3 Hcore4 Hpr4 H10' Hval' K4.
  assert (Hfxk3 : rl_fxk [10; 13; 14; 15] fx fx3)
  by (apply (m2k_fxk_trans _ _ _ _ _ HfxA Hfx3); intros z Hz; cbn in Hz |- *; tauto).
  apply (m2f_walk3 (fx := fx3) B MT MTL LAWS cx POST ly4 S4 W4 regs4 mem4 md4
    (Nearest.nearest (Cursor.rd32 (Model.e_body ent)) Nearest.INT32_MIN Nearest.INT32_MAX) Hpre Hcore4
    ltac:(rewrite (Hpr4 9 ltac:(unfold acallee_saved; lia)), (Hpr3 9 ltac:(unfold acallee_saved; lia)); exact A9)
    H10' Hval').
  + (* None: MAL *)
    intros Hn ly5 S5 W5 regs5 mem5 md5 Hcore5 Hpr5 K5.
    apply (m2f_exit_mal cx POST rec fx2 fx3 ly2 S2 W2 regs2 mem2 md2 ly5 S5 W5 regs5 mem5 md5 Hpre HMAL Hbase Hrole
      Hlen HatL Hcore5 (aregs_preserved_trans _ _ _ (aregs_preserved_trans _ _ _ Hpr3 Hpr4) Hpr5) Hfxk3).
    * intros a Hw. pose proof (HwzK a Hw) as Ha. unfold m2k_wz in Hw.
      rewrite (K5 a Ha), (K4 a Ha ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK in *; lia)
        ltac:(intros (Hne & _); exact (Hne Hn))).
      exact (K3 a Ha).
    * rewrite HPA, (m2k_expect_float ent Hwf Hty Hge), Hn. reflexivity.
  + (* Some r: the value tail *)
    intros r Hr ly5 S5 W5 regs5 mem5 md5 Hcore5 Hpr5 K5 H12.
    assert (HK : forall a, ~ m2k_wz cx a -> aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W2) mem2 a).
    { intros a Hw. pose proof (HwzK a Hw) as Ha. unfold m2k_wz in Hw.
      rewrite (K5 a Ha), (K4 a Ha ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK in *; lia)
        ltac:(intros (_ & Hx); lia)).
      exact (K3 a Ha). }
    destruct (m2f_cut cx rec fx2 fx3 ly2 S2 W2 regs2 mem2 md2 ly5 S5 W5 regs5 mem5 md5 Hpre Hbase Hrole Hlen HatL
      Hcore5 (aregs_preserved_trans _ _ _ (aregs_preserved_trans _ _ _ Hpr3 Hpr4) Hpr5) Hfxk3 HK)
    as (HCB5 & HRA5 & HAT5).
    pose proof (m2k_nearest_range _ _ Hr) as Hrr.
    assert (Hrm : (0 <= r /\ r mod 2 ^ 64 = r) \/ (r < 0 /\ r mod 2 ^ 64 = r + 2 ^ 64)).
    { destruct (Z_le_gt_dec 0 r).
      - left. split; [lia|]. apply Z.mod_small. lia.
      - right. split; [lia|]. rewrite <- (Z.mod_add r 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    assert (HPr : rs_PA rsegs cx rec = Role.flag_rc r) by (rewrite HPA, (m2k_expect_float ent Hwf Hty Hge), Hr; reflexivity).
    apply (HV fx3 ly5 S5 W5 regs5 mem5 md5 (r mod 2 ^ 64) HCB5 HRA5 HAT5 H12 ltac:(apply Z.mod_pos_bound; lia)).
    * intros Hv2. assert (Hr01 : 0 <= r < 2) by lia.
      destruct (m2k_flag_small r Hr01) as (Hs1 & w & Hw1 & Hw2).
      rewrite HPr. split; [exact Hs1|]. rewrite Hw1. unfold rs_rcell. lia.
    * intros Hv2. rewrite HPr, (m2k_flag_big r ltac:(lia)). split; reflexivity.
Qed.
End f.

Print Assumptions rl_m02_key_float.
