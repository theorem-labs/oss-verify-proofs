(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 676 of its 730 lines of code are new or changed and 2635 lines of the source are left out. *)
(* talk on image A: the entry piece TK_ENTRY of lib/A/Prog/talk_defs.v, the lemma tk_entry_ok.
   The walk is cut at +0x5c, the first instrumented check, so that the frame, the .got word of the shadow base and
   its cell are the only regions of the first state and the model block the only region of the second:
   - te_e_ss (+0x00 .. +0x58): the 144-byte frame, s2 := alias_n, s0 := alias, s3 := kind_n, s1 := kind,
     s5 := len, s7 := the shadow base through the .got cell, s4 := m. It writes the thirteen saved words only;
   - te_ss (+0x5c, the model block at s4 = m, the shadow checks of a0 = m and s4 = m): socket_errno <> 0 stores
     0 at m and leaves at +0xb4 with a1 = - socket_errno; else send_errno <> 0 stores 0 at m + 4 and leaves the
     same way; else n_req decides between the chunk loop set-up +0x16c (TK_CL0, the ring full) and the call of
     checked_memcpy at +0x12c (TK_AT_CP1).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk talk_c talk_defs talk_kit talk_spec talk_ret talk_chunk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the cut at the first instrumented check *)
Definition TP_S : Z := AF_talk + 0x5c.
(* the entry: the frame, the .got word and its cell (atom 32 = the shadow base) *)
Definition te_e_ss : sstate :=
  mkSS TP_E sr_atoms [stack_region 144; got_regionP; bcell_regionP 32] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
(* +0x5c: the model block at s4 = m; socket_errno and send_errno writable, n_req read only *)
Definition te_R0 : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 8 0 8 [tk_ch 0 4 (SOff 49 0); tk_ch 4 4 (SOff 50 0)].
Definition te_R1 : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0x2090 0x2094 0 0 [tk_ch 0x2090 4 (SOff 51 0)].
Definition te_ss : sstate :=
  tk_ss TP_S [] [te_R0; te_R1]
    [(10%nat, mkAF 0 (kHighMemEnd - 1 - MD_SIZE) 0); (20%nat, mkAF 0 (kHighMemEnd - 1 - MD_SIZE) 0);
     (49%nat, mkAF 0 (2 ^ 31 - 1) 0); (50%nat, mkAF 0 (2 ^ 31 - 1) 0); (51%nat, mkAF 0 16 0)].
(* the shadow of the model block, through a0 and through s4 *)
Definition te_SH : list shent := [mkSHE 10 0 MD_SIZE; mkSHE 20 0 MD_SIZE].

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Variable c : tkc.
Hypothesis HC : tk_call SK B c.
#[local] Notation W := (tc_W c).
#[local] Notation memc := (tc_memc c).
#[local] Notation regs0 := (tc_regs0 c).
#[local] Notation mbs := (tc_mbs c).
#[local] Notation kbs := (tc_kbs c).
#[local] Notation req := (tc_req c).

Ltac te_in := repeat (first [left; reflexivity | right]).
Ltac te_keep RK r K := pose proof (RK r ltac:(te_in)) as K; cbn [ms_regs restrict] in K.
Ltac te_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
Ltac te_zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32);
  try change (Z.of_N 8) with 8; try change (Z.of_N 4) with 4; lia.

(* the piece's own values: socket_errno, send_errno, n_req *)
Definition te_xs : list word :=
  [w64 (md_socket_errno mbs); w64 (md_send_errno mbs); w64 (md_n_req mbs)].

Lemma te_arg : forall (i : Z) (r : bv 5), r = Z_to_bv 5 (10 + i) -> getr regs0 r = w64 (aarg regs0 i).
Proof. intros i r ->. unfold aarg, argZ, w64. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* a byte of the frame is a byte the caller lets talk write *)
Lemma te_ajw_stk : forall a, tk_sp c - 144 <= a < tk_sp c ->
  ajw B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_lyc c) (tc_Sc c)
    (tc_own c) a.
Proof.
  intros a Ha. destruct (tk_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & H16 & HXO).
  unfold TALK_AK, TALK_AFRAME, ESTACK in Hlo.
  left. split; [left; lia | lia].
Qed.

(* the buffers at the call, with no attribute seen yet *)
Lemma te_bufs0 : tk_bufs c memc no_attrs.
Proof.
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & HBK & HBA & _).
  split; [exact HBK|]. split; [exact HBA|].
  split; [intros pay Hp; discriminate Hp|]. split; [intros pay Hp; discriminate Hp|].
  split; intros _ _ _ i _; reflexivity.
Qed.

(* a frame word of the end state's stack region *)
Lemma te_fword : forall E m cs lo hi wlo whi od (n : nat) (w : word),
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2) = tk_sp c ->
  In (YP09.mkChunk (od - 144) (CVal 8 (SOff n 0))) cs -> ew E n = w ->
  val_mem SEGS m (tk_sp c - 144 + od) 8 (bv_unsigned w).
Proof.
  intros E m cs lo hi wlo whi od n w HR Hsp Hin Hn.
  replace (tk_sp c - 144 + od) with (tk_sp c + (od - 144)) by lia.
  refine (field_of_region E m 2 (tk_sp c) cs lo hi wlo whi (od - 144) 8%N (SOff n 0) (bv_unsigned w)
    HR Hsp Hin _ _ _).
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
Qed.

(* ---- THE ENTRY STATE ---- *)
Lemma te_entry_st :
  st_ok_pi SEGS VAL (Eimg (Ereg regs0 (tk_xe c))) te_e_ss
    (restrict (w_H W) (mkst regs0 (Z_to_bv 64 (BASE + TP_E)) memc (seg_rom SEGS))).
Proof.
pose proof HC as ((HJ & _) & _).
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (tk_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & H16 & HXO').
destruct (tk_sp_rng SK B c HC) as (S0 & S1 & S2 & S3).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS (tc_lyc c) (tc_Sc c) W memc (tc_mdc c) HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
assert (V1 : VAL (A_OBJ 1) = 0xa19d0) by (rewrite (lv_obj LV 1) by (unfold link_nobj; lia); reflexivity).
assert (V64 : VAL (A_OBJ 64) = 0xaa438) by (rewrite (lv_obj LV 64) by (unfold link_nobj; lia); reflexivity).
rewrite V1, V64 in Kgot. rewrite V64 in Kcell.
set (E := Eimg (Ereg regs0 (tk_xe c))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs0 2)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs0 _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 0)).
assert (Usp : bv_unsigned (ew E 2) = tk_sp c) by (rewrite E2; reflexivity).
assert (Ugot : bv_unsigned (ew E (A_OBJ 1)) = 0xa19d0)
  by (rewrite (HEI (A_OBJ 1)) by (unfold A_OBJ, A_TEXT, A_LIM; lia); exact V1).
assert (Ucell : bv_unsigned (ew E (A_OBJ 64)) = 0xaa438)
  by (rewrite (HEI (A_OBJ 64)) by (unfold A_OBJ, A_TEXT, A_LIM; lia); exact V64).
rewrite restrict_mkst_fx. unfold te_e_ss. apply pa_entry_st_ok_full.
- unfold E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres.
    unfold TALK_AK, TALK_AFRAME, ESTACK in Hlo. lia.
  + rewrite Ugot. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa19d0 0 8 (SOff (A_OBJ 64) 0) 0xaa438);
      [ cbn [sv_denot]; rewrite Ucell, Z.add_0_r; reflexivity | te_zrng | te_zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + rewrite Ucell. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xaa438 0 8 (SOff 32 0) SHADOW_OFF);
      [ cbn [sv_denot]; rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia);
        rewrite Z.add_0_r; reflexivity
      | unfold SHADOW_OFF; te_zrng | te_zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Usp, Ugot, Ucell.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the model block across a run that writes nothing of it, read back from te_R0 *)
Lemma te_keep_blk : forall mem mem',
  amodel_at SEGS (rdW W mem) (tk_m c) mbs ->
  val_mem SEGS (rdW W mem') (tk_m c + MD_SOCKET_ERRNO) 4 (md_socket_errno mbs) ->
  val_mem SEGS (rdW W mem') (tk_m c + MD_SEND_ERRNO) 4 (md_send_errno mbs) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_m c <= a < tk_m c + 8) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  amodel_at SEGS (rdW W mem') (tk_m c) mbs.
Proof.
  intros mem mem' HM V0 V4 UN PR.
  destruct (tk_m_facts SK B c HC) as (Hm0 & Hmhi & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (ck_mfield c mem mbs MD_SOCKET_ERRNO 4%nat HM ltac:(unfold MD_SOCKET_ERRNO; lia)
    ltac:(unfold MD_SOCKET_ERRNO, MD_SIZE; cbn; lia)) as W0.
  pose proof (ck_mfield c mem mbs MD_SEND_ERRNO 4%nat HM ltac:(unfold MD_SEND_ERRNO; lia)
    ltac:(unfold MD_SEND_ERRNO, MD_SIZE; cbn; lia)) as W4.
  change (Z.of_nat 4) with 4 in W0, W4.
  apply (amodel_kept SEGS (rdW W mem) (rdW W mem') (tk_m c) mbs HM).
  - intros i Hi. destruct (Z_lt_le_dec i 8) as [H8|H8].
    + destruct (Z_lt_le_dec i 4) as [H4|H4].
      * replace (tk_m c + i) with (tk_m c + MD_SOCKET_ERRNO + Z.of_nat (Z.to_nat i))
          by (unfold MD_SOCKET_ERRNO; lia).
        rewrite (V0 (Z.to_nat i) ltac:(lia)), (W0 (Z.to_nat i) ltac:(lia)). reflexivity.
      * replace (tk_m c + i) with (tk_m c + MD_SEND_ERRNO + Z.of_nat (Z.to_nat (i - 4)))
          by (unfold MD_SEND_ERRNO; lia).
        rewrite (V4 (Z.to_nat (i - 4)) ltac:(lia)), (W4 (Z.to_nat (i - 4)) ltac:(lia)). reflexivity.
    + apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem').
      apply UN; [unfold MD_SIZE in *; lia | cbv beta; lia].
  - intros i Hi. apply (writable_kept (w_H W) mem mem' (tk_m c + i) (PR (tk_m c + i))).
    exact (ck_mwr c mem mbs HM i Hi).
Qed.

(* one run of the entry that leaves the model block alone *)
Lemma te_adv : forall E regs mem md regs' mem' md',
  tk_inv SK B c regs mem md -> amodel_at SEGS (rdW W mem) (tk_m c) mbs -> tk_bufs c mem no_attrs ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c)
    (tc_W0 c) (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W mem' md' (tc_k c) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_m c <= a < tk_m c + 8) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  mem_grows (rdW W mem) (rdW W mem') ->
  bv_unsigned (ew E 20) = tk_m c ->
  ew E 49 = w64 (md_socket_errno mbs) -> ew E 50 = w64 (md_send_errno mbs) ->
  region_ok SEGS E (rdW W mem') te_R0 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  tk_inv SK B c regs' mem' md' /\ amodel_at SEGS (rdW W mem') (tk_m c) mbs /\ tk_bufs c mem' no_attrs.
Proof.
  intros E regs mem md regs' mem' md' HI HM HB HJ Hfd Hfs UN HG U20 F49 F50 HR R2 R3 R4.
  pose proof (ck_wf SK B c HC) as (_ & HMW & _).
  pose proof HMW as (_ & _ & HSK & HSD & _).
  destruct (tk_m_facts SK B c HC) as (Hm0 & Hmhi & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & PRm).
  assert (V0 : val_mem SEGS (rdW W mem') (tk_m c + MD_SOCKET_ERRNO) 4 (md_socket_errno mbs)).
  { eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
      [ exact HR | exact U20 | te_in | apply ck_den0; [exact F49 | lia] | te_zrng | te_zrng ]. }
  assert (V4 : val_mem SEGS (rdW W mem') (tk_m c + MD_SEND_ERRNO) 4 (md_send_errno mbs)).
  { eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
      [ exact HR | exact U20 | te_in | apply ck_den0; [exact F50 | lia] | te_zrng | te_zrng ]. }
  split; [|split].
  - apply (tk_inv_step SK B c HC regs mem md regs' mem' md'
      (fun a => tk_m c <= a < tk_m c + 8) HI HJ Hfd Hfs UN);
      [ intros a Ha; right; apply ck_ewr_m; cbv beta in Ha; unfold MD_SIZE in *; lia
      | intros a Hp; exact (apresent_grows _ _ _ _ HG Hp) | exact R2 | exact R3 | exact R4 ].
  - exact (te_keep_blk mem mem' HM V0 V4 UN (fun a Hp => apresent_grows _ _ _ _ HG Hp)).
  - apply (ck_bufs_keep SK B c HC mem mem' no_attrs HB);
      [ intros a Ha Hoff Hwin; apply UN; [exact Ha | cbv beta; unfold MD_SIZE in *; lia]
      | intros a Hp; exact (apresent_grows _ _ _ _ HG (PRm a Hp)) ].
Qed.

Lemma te_same : forall regs xs (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot (tk_E c regs xs) (SOff n 0) = getr regs r.
Proof.
  intros regs xs n r Hn Hr. cbn [sv_denot]. rewrite (tk_E_reg c regs xs n r Hn Hr), Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
Qed.

(* the destination of checked_memcpy +0x12c: m + 12 + 512 n *)
Lemma te_den_slot : forall E n, ew E 20 = w64 (tk_m c) -> ew E 51 = w64 n ->
  0 <= tk_m c -> tk_m c + MD_SIZE <= kHighMemEnd - 1 -> 0 <= n <= 15 ->
  sv_denot E (SAlu ALU_ADD (SOff 20 12) (SAlu ALU_SLL (SOff 51 0) (SLit 9))) =
  w64 (tk_m c + MD_REQ + NL_SENT_LEN * n).
Proof.
  intros E n E20 E51 Hm0 Hmhi Hn.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite (ck_U0 E 51 n E51) by lia. rewrite !U_lit by lia.
  rewrite (ck_Uoff E 20 (tk_m c) 12 E20) by (unfold MD_SIZE in *; lia).
  change (Z.land 9 63) with 9. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 9) with 512.
  unfold zcanon, M64, MD_REQ, NL_SENT_LEN, MD_SIZE in *. rewrite !(Z.mod_small _ (2 ^ 64)); lia.
Qed.

(* an exit store of 0 into socket_errno (z = 0) or send_errno (z = 4) *)
Lemma te_zero_fld : forall mem mem' (z o : Z),
  (z = 0 /\ o = 4) \/ (z = 4 /\ o = 0) ->
  amodel_at SEGS (rdW W mem) (tk_m c) mbs ->
  val_mem SEGS (rdW W mem') (tk_m c + z) 4 0 ->
  val_mem SEGS (rdW W mem') (tk_m c + o) 4 (rdn mbs o 4) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_m c <= a < tk_m c + 8) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  amodel_at SEGS (rdW W mem') (tk_m c) (bput mbs z (lev 4 0)).
Proof.
  intros mem mem' z o Hzo HM VZ VO UN PR.
  destruct (tk_m_facts SK B c HC) as (Hm0 & Hmhi & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (ck_mfield c mem mbs o 4%nat HM ltac:(destruct Hzo as [(?&?)|(?&?)]; lia)
    ltac:(unfold MD_SIZE; destruct Hzo as [(?&?)|(?&?)]; cbn; lia)) as WO.
  change (Z.of_nat 4) with 4 in WO.
  apply (amodel_store SEGS (rdW W mem) (rdW W mem') (tk_m c) mbs z 4%nat 0 HM);
    [ destruct Hzo as [(?&?)|(?&?)]; lia
    | unfold MD_SIZE; destruct Hzo as [(?&?)|(?&?)]; cbn; lia
    | | exact VZ | ].
  - intros i Hi Hni. destruct (Z_lt_le_dec i 8) as [H8|H8].
    + replace (tk_m c + i) with (tk_m c + o + Z.of_nat (Z.to_nat (i - o)))
        by (destruct Hzo as [(?&?)|(?&?)]; lia).
      rewrite (VO (Z.to_nat (i - o)) ltac:(destruct Hzo as [(?&?)|(?&?)]; lia)),
              (WO (Z.to_nat (i - o)) ltac:(destruct Hzo as [(?&?)|(?&?)]; lia)). reflexivity.
    + apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem').
      apply UN; [unfold MD_SIZE in *; lia | cbv beta; lia].
  - intros i Hi. apply (writable_kept (w_H W) mem mem' (tk_m c + i) (PR (tk_m c + i))).
    exact (ck_mwr c mem mbs HM i Hi).
Qed.

(* the run that stores 0 and leaves at +0xb4 *)
Lemma te_exit_step : forall regs mem md regs' mem' md' (z o : Z),
  (z = 0 /\ o = 4) \/ (z = 4 /\ o = 0) ->
  tk_inv SK B c regs mem md -> amodel_at SEGS (rdW W mem) (tk_m c) mbs -> tk_bufs c mem no_attrs ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c)
    (tc_W0 c) (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W mem' md' (tc_k c) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_m c <= a < tk_m c + 8) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  mem_grows (rdW W mem) (rdW W mem') ->
  val_mem SEGS (rdW W mem') (tk_m c + z) 4 0 ->
  val_mem SEGS (rdW W mem') (tk_m c + o) 4 (rdn mbs o 4) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  tk_inv SK B c regs' mem' md' /\ amodel_at SEGS (rdW W mem') (tk_m c) (bput mbs z (lev 4 0))
  /\ tk_bufs c mem' no_attrs.
Proof.
  intros regs mem md regs' mem' md' z o Hzo HI HM HB HJ Hfd Hfs UN HG VZ VO R2 R3 R4.
  destruct (tk_m_facts SK B c HC) as (Hm0 & Hmhi & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & PRm).
  split; [|split].
  - apply (tk_inv_step SK B c HC regs mem md regs' mem' md'
      (fun a => tk_m c <= a < tk_m c + 8) HI HJ Hfd Hfs UN);
      [ intros a Ha; right; apply ck_ewr_m; cbv beta in Ha; unfold MD_SIZE in *; lia
      | intros a Hp; exact (apresent_grows _ _ _ _ HG Hp) | exact R2 | exact R3 | exact R4 ].
  - exact (te_zero_fld mem mem' z o Hzo HM VZ VO UN (fun a Hp => apresent_grows _ _ _ _ HG Hp)).
  - apply (ck_bufs_keep SK B c HC mem mem' no_attrs HB);
      [ intros a Ha Hoff Hwin; apply UN; [exact Ha | cbv beta; unfold MD_SIZE in *; lia]
      | intros a Hp; exact (apresent_grows _ _ _ _ HG (PRm a Hp)) ].
Qed.

Ltac te_win U :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
      first [ exfalso; clear - Hrr; lia | rewrite U in Hrr; clear - Hrr; lia ] | ]);
  destruct Hin.
Ltac te_kept HFr U UN :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => tk_m c <= a < tk_m c + 8) HFr
    ltac:(te_win U)) as UN.
Ltac te_awr_m U :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_x_cons;
  [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U in Ha;
    apply (ck_ajw_m SK B c HC); unfold MD_SIZE in Ha |- *; lia |];
  apply awr_ok_x_cons;
  [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; exfalso; clear - Ha; lia |];
  apply awr_ok_x_nil.

Ltac te_kr HSx r n Hname :=
  te_reg HSx r Hname;
  rewrite (te_same _ _ n r ltac:(lia) ltac:(reflexivity)) in Hname.

(* ---- THE PIECE ---- *)
Lemma tk_entry_ok : TK_RET SK B c -> TK_AT_CP1 SK B c -> TK_CL0 SK B c -> TK_ENTRY SK B c.
Proof.
intros HRET HCP1 HCL0.
pose proof (ck_wf SK B c HC) as (HNW & HMW & HML & HKL & HRQ).
destruct (tk_m_facts SK B c HC) as (Hm0 & Hmhi & Hm2 & Hmg & Hmf & Hmra & Hmh & Hmbs).
destruct (tk_r_facts SK B c HC) as (Hr0 & Hrlen & Hramr & Hrhi & Hrf & Hrp & Hrra & Hrh & Hrq & Hrl).
destruct (tk_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & H16 & HXO).
destruct (tk_sp_rng SK B c HC) as (S0 & S1 & S2 & S3).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HC as ((HJ0 & _ & _ & Hret & _ & Hgp & Htp & _) & _).
pose proof HMW as (HNRB & HNXB & HSKB & HSDB & _).
unfold NL_SENT_MAX in HNRB.
pose proof te_bufs0 as HB0.
unfold tk_goal.
(* ---- +0x00 .. +0x58 ---- *)
pose proof te_entry_st as HS.
set (E0 := Eimg (Ereg regs0 (tk_xe c))) in *.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (ER : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs0 r)
  by (intros n r Hn Hr; unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_nat regs0 _ n r Hr)).
assert (E32 : ew E0 32 = w64 SHADOW_OFF)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 0)).
assert (Usp0 : bv_unsigned (ew E0 2) = tk_sp c) by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E0 (rdW W memc)) by constructor.
pose proof (paj_run_x SK B LAWS (tc_G c) (ck_HGX SK B c HC) (tc_XO c) (tc_OUT c)) as RUN.
pose proof (paj_run_to_x SK B LAWS (tc_G c) (ck_HGX SK B c HC) (tc_XO c) (tc_OUT c)) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
paj_run_to_tok RUNTO HS HJ0 SHOK tk_span TP_S.
- (* the frame is the only write window *)
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp0 in Ha;
      apply te_ajw_stk; lia |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; exfalso; clear - Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; exfalso; clear - Ha; lia|].
  apply awr_ok_x_nil.
- lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => tk_sp c - 144 <= a < tk_sp c) HFr
    ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin];
            [ injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
              first [ exfalso; clear - Hrr; lia | rewrite Usp0 in Hrr; clear - Hrr; lia ] | ]);
          destruct Hin)) as UN1.
  pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HRf.
  assert (HFV : Forall (fun p => val_mem SEGS (rdW W (ms_mem ms1)) (tk_sp c - 144 + fst p) 8
                   (bv_unsigned (snd p))) (tk_frame_vals c)).
  { unfold tk_frame_vals. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (eapply te_fword; [exact HRf | exact Usp0 | te_in | apply ER; [lia | reflexivity]]). }
  te_reg HS (2%bv : bv 5) Q2. te_reg HS (3%bv : bv 5) Q3. te_reg HS (4%bv : bv 5) Q4.
  te_reg HS (8%bv : bv 5) Q8. te_reg HS (9%bv : bv 5) Q9. te_reg HS (18%bv : bv 5) Q18.
  te_reg HS (19%bv : bv 5) Q19. te_reg HS (20%bv : bv 5) Q20. te_reg HS (21%bv : bv 5) Q21.
  te_reg HS (23%bv : bv 5) Q23. te_reg HS (10%bv : bv 5) Q10. te_reg HS (11%bv : bv 5) Q11.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (MD1 := mdq) end.
  assert (R2 : getr (ms_regs ms1) 2 = w64 (tk_sp c - 144)).
  { rewrite Q2. cbn [sv_denot]. rewrite (ER 2%nat 2%bv) by (lia || reflexivity). unfold tk_sp, spZ, w64.
    f_equal; lia. }
  assert (R3 : getr (ms_regs ms1) 3 = getr regs0 3)
    by (rewrite Q3; cbn [sv_denot]; rewrite (ER 3%nat 3%bv) by (lia || reflexivity);
        rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (R4 : getr (ms_regs ms1) 4 = getr regs0 4)
    by (rewrite Q4; cbn [sv_denot]; rewrite (ER 4%nat 4%bv) by (lia || reflexivity);
        rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (HI1 : tk_inv SK B c (ms_regs ms1) (ms_mem ms1) MD1).
  { split; [exact HJ0|]. split; [unfold MD1; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity|].
    split; [unfold MD1; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity|].
    split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact HFV|].
    split.
    - intros a Ha Hw He. apply UN1; [exact Ha | cbv beta; unfold TALK_AK, TALK_AFRAME, ESTACK in *; lia].
    - intros a Hp. exact (apresent_grows _ _ _ _ HG Hp). }
  assert (HB1 : tk_bufs c (ms_mem ms1) no_attrs).
  { apply (ck_bufs_keep SK B c HC memc (ms_mem ms1) no_attrs HB0).
    - intros a Ha Hoff Hwin. apply UN1; [exact Ha | cbv beta; unfold TALK_AK, TALK_AFRAME, ESTACK in *; lia].
    - intros a Hp. exact (apresent_grows _ _ _ _ HG Hp). }
  assert (R10 : getr (ms_regs ms1) 10 = w64 (tk_m c))
    by (rewrite Q10; cbn [sv_denot]; rewrite (ER 10%nat (Z_to_bv 5 (10 + 0))) by (lia || reflexivity);
        rewrite Z.add_0_r; rewrite (te_arg 0 (Z_to_bv 5 (10 + 0)) eq_refl); unfold w64;
        apply Z_to_bv_bv_unsigned).
  assert (R20 : getr (ms_regs ms1) 20 = w64 (tk_m c))
    by (rewrite Q20; cbn [sv_denot]; rewrite (ER 10%nat (Z_to_bv 5 (10 + 0))) by (lia || reflexivity);
        rewrite Z.add_0_r; rewrite (te_arg 0 (Z_to_bv 5 (10 + 0)) eq_refl); unfold w64;
        apply Z_to_bv_bv_unsigned).
  assert (R23 : getr (ms_regs ms1) 23 = w64 SHADOW_OFF)
    by (rewrite Q23; cbn [sv_denot]; rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia);
        rewrite Z.add_0_r; reflexivity).
  assert (HR0 : tk_rs0 c (ms_regs ms1)).
  { split.
    - rewrite Q8. cbn [sv_denot]. rewrite (ER 15%nat (Z_to_bv 5 (10 + 5))) by (lia || reflexivity).
      rewrite Z.add_0_r, (te_arg 5 (Z_to_bv 5 (10 + 5)) eq_refl). unfold w64. apply Z_to_bv_bv_unsigned.
    - split.
      + rewrite Q9. cbn [sv_denot]. rewrite (ER 13%nat (Z_to_bv 5 (10 + 3))) by (lia || reflexivity).
        rewrite Z.add_0_r, (te_arg 3 (Z_to_bv 5 (10 + 3)) eq_refl). unfold w64. apply Z_to_bv_bv_unsigned.
      + exact R23. }
  assert (HRN : tk_rsn c (ms_regs ms1)).
  { split.
    - rewrite Q18. cbn [sv_denot]. rewrite (ER 16%nat (Z_to_bv 5 (10 + 6))) by (lia || reflexivity).
      rewrite Z.add_0_r, (te_arg 6 (Z_to_bv 5 (10 + 6)) eq_refl). unfold w64. apply Z_to_bv_bv_unsigned.
    - rewrite Q19. cbn [sv_denot]. rewrite (ER 14%nat (Z_to_bv 5 (10 + 4))) by (lia || reflexivity).
      rewrite Z.add_0_r, (te_arg 4 (Z_to_bv 5 (10 + 4)) eq_refl). unfold w64. apply Z_to_bv_bv_unsigned. }
  assert (R21 : getr (ms_regs ms1) 21 = w64 (tk_len c))
    by (rewrite Q21; cbn [sv_denot]; rewrite (ER 12%nat (Z_to_bv 5 (10 + 2))) by (lia || reflexivity);
        rewrite Z.add_0_r, (te_arg 2 (Z_to_bv 5 (10 + 2)) eq_refl); unfold w64;
        apply Z_to_bv_bv_unsigned).
  assert (R11 : getr (ms_regs ms1) 11 = w64 (tk_r c))
    by (rewrite Q11; cbn [sv_denot]; rewrite (ER 11%nat (Z_to_bv 5 (10 + 1))) by (lia || reflexivity);
        rewrite Z.add_0_r, (te_arg 1 (Z_to_bv 5 (10 + 1)) eq_refl); unfold w64;
        apply Z_to_bv_bv_unsigned).
  assert (Hbufk : forall i, 0 <= i < tk_len c ->
            aview SEGS (w_H W) (ms_mem ms1) (tk_r c + i) = aview SEGS (w_H W) memc (tk_r c + i)).
  { intros i Hi. apply UN1; [unfold amem_range, kLowMemEnd, kHighMemBeg in *; lia|].
    cbv beta. unfold apart_frame, tk_sp, TALK_AK, TALK_AFRAME, ESTACK in *. lia. }
  assert (HM1 : amodel_at SEGS (rdW W (ms_mem ms1)) (tk_m c) mbs).
  { apply (amodel_kept SEGS (rdW W memc) (rdW W (ms_mem ms1)) (tk_m c) mbs Hmbs).
    - intros i Hi. apply (mbyte_of_aview SEGS (w_H W) (w_H W) memc (ms_mem ms1)).
      apply UN1; [unfold MD_SIZE in *; lia
                 | cbv beta; unfold apart_frame, tk_sp, TALK_AK, TALK_AFRAME, ESTACK, MD_SIZE in *; lia].
    - intros i Hi. pose proof HI1 as (_ & _ & _ & _ & _ & _ & _ & _ & PR1).
      apply (writable_kept (w_H W) memc (ms_mem ms1) (tk_m c + i) (PR1 (tk_m c + i))).
      exact (ck_mwr c memc mbs Hmbs i Hi). }
  clear HF HFr HG UN1 HRf HS SHOK HEI Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q23 Q10 Q11.
  (* ---- +0x5c: the model block ---- *)
  assert (E10 : ew (tk_E c (ms_regs ms1) te_xs) 10 = w64 (tk_m c))
    by (rewrite (tk_E_reg c (ms_regs ms1) te_xs 10 10%bv) by (lia || reflexivity); exact R10).
  assert (U10 : bv_unsigned (ew (tk_E c (ms_regs ms1) te_xs) 10) = tk_m c)
    by (rewrite E10; apply ck_uw; unfold MD_SIZE in *; lia).
  assert (E20 : ew (tk_E c (ms_regs ms1) te_xs) 20 = w64 (tk_m c))
    by (rewrite (tk_E_reg c (ms_regs ms1) te_xs 20 20%bv) by (lia || reflexivity); exact R20).
  assert (U20 : bv_unsigned (ew (tk_E c (ms_regs ms1) te_xs) 20) = tk_m c)
    by (rewrite E20; apply ck_uw; unfold MD_SIZE in *; lia).
  assert (F49 : ew (tk_E c (ms_regs ms1) te_xs) 49 = w64 (md_socket_errno mbs))
    by exact (tk_E_xs c (ms_regs ms1) te_xs 0%nat ltac:(lia)).
  assert (F50 : ew (tk_E c (ms_regs ms1) te_xs) 50 = w64 (md_send_errno mbs))
    by exact (tk_E_xs c (ms_regs ms1) te_xs 1%nat ltac:(lia)).
  assert (F51 : ew (tk_E c (ms_regs ms1) te_xs) 51 = w64 (md_n_req mbs))
    by exact (tk_E_xs c (ms_regs ms1) te_xs 2%nat ltac:(lia)).
  assert (E21 : ew (tk_E c (ms_regs ms1) te_xs) 21 = w64 (tk_len c))
    by (rewrite (tk_E_reg c (ms_regs ms1) te_xs 21 21%bv) by (lia || reflexivity); exact R21).
  pose proof (tk_E_env c (ms_regs ms1) te_xs) as HEI.
  assert (HS : st_ok_pi SEGS VAL (tk_E c (ms_regs ms1) te_xs) te_ss
      (restrict (w_H W) (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + TP_S)) (ms_mem ms1) (seg_rom SEGS)))).
  { unfold te_ss. apply (tk_st_ok SK B LV c HC (ms_regs ms1) (ms_mem ms1) MD1 te_xs TP_S).
    - exact HI1.
    - exact R23.
    - apply Forall_nil.
    - vm_compute; reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold te_R0, tk_ch, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U20. split; [lia|]. split; [unfold MD_SIZE in *; lia|].
        split; [intros o Ho; apply (ck_mwr c (ms_mem ms1) mbs HM1); unfold MD_SIZE; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS _ _ (tk_m c) 0 4 (SOff 49 0) (md_socket_errno mbs));
            [ apply ck_den0; [exact F49 | lia] | te_zrng | te_zrng |].
          pose proof (ck_mfield c (ms_mem ms1) mbs MD_SOCKET_ERRNO 4%nat HM1
            ltac:(unfold MD_SOCKET_ERRNO; lia) ltac:(unfold MD_SOCKET_ERRNO, MD_SIZE; cbn; lia)) as HV.
          change (Z.of_nat 4) with 4 in HV. exact HV.
        * apply (chunk_ok_val SEGS _ _ (tk_m c) 4 4 (SOff 50 0) (md_send_errno mbs));
            [ apply ck_den0; [exact F50 | lia] | te_zrng | te_zrng |].
          pose proof (ck_mfield c (ms_mem ms1) mbs MD_SEND_ERRNO 4%nat HM1
            ltac:(unfold MD_SEND_ERRNO; lia) ltac:(unfold MD_SEND_ERRNO, MD_SIZE; cbn; lia)) as HV.
          change (Z.of_nat 4) with 4 in HV. exact HV.
      + unfold te_R1, tk_ch, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U20. split; [lia|]. split; [unfold MD_SIZE in *; lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS _ _ (tk_m c) 8336 4 (SOff 51 0) (md_n_req mbs));
          [ apply ck_den0; [exact F51 | lia] | te_zrng | te_zrng |].
        pose proof (ck_mfield c (ms_mem ms1) mbs MD_N_REQ 4%nat HM1
          ltac:(unfold MD_N_REQ; lia) ltac:(unfold MD_N_REQ, MD_SIZE; cbn; lia)) as HV.
        change (Z.of_nat 4) with 4 in HV. exact HV.
    - apply pairwise_disjoint_of_extents. unfold te_R0, te_R1, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - refine (conj _ (conj _ (conj _ (conj _ (conj _ I))))); unfold afact_ok; cbn [af_lo af_hi af_al2].
      + rewrite U10, Z.pow_0_r, Z.mod_1_r. unfold MD_SIZE in *. lia.
      + rewrite U20, Z.pow_0_r, Z.mod_1_r. unfold MD_SIZE in *. lia.
      + rewrite F49, (ck_uw (md_socket_errno mbs)) by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
      + rewrite F50, (ck_uw (md_send_errno mbs)) by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
      + rewrite F51, (ck_uw (md_n_req mbs)) by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  assert (SHOK : sh_ok SEGS tk_Bx te_SH (tk_E c (ms_regs ms1) te_xs) (rdW W (ms_mem ms1))).
  { unfold te_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (ck_shent SK B c HC (ms_regs ms1) (ms_mem ms1) MD1 te_xs 10%nat 10%bv (tk_m c) MD_SIZE HI1
        ltac:(lia) ltac:(reflexivity) R23 R10);
        [ lia | unfold MD_SIZE; lia | lia
        | unfold amem_range, kLowMemEnd, kHighMemBeg in *; destruct Hm2 as [Hq|Hq]; [left|right]; lia
        | exact Hmra ].
    - apply (ck_shent SK B c HC (ms_regs ms1) (ms_mem ms1) MD1 te_xs 20%nat 20%bv (tk_m c) MD_SIZE HI1
        ltac:(lia) ltac:(reflexivity) R23 R20);
        [ lia | unfold MD_SIZE; lia | lia
        | unfold amem_range, kLowMemEnd, kHighMemBeg in *; destruct Hm2 as [Hq|Hq]; [left|right]; lia
        | exact Hmra ]. }
  pose proof HI1 as (HJ1 & _).
  (* +0x5c .. +0x6c: the check and the load of socket_errno, then `beqz` *)
  paj_run_tok RUN HS HJ1 SHOK tk_span; [te_awr_m U20|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  te_kept HFr U20 UN2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (MD2 := mdq) end.
  te_kr HS (2%bv : bv 5) 2%nat Ka2. te_kr HS (3%bv : bv 5) 3%nat Ka3. te_kr HS (4%bv : bv 5) 4%nat Ka4.
  pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HRg2.
  destruct (te_adv (tk_E c (ms_regs ms1) te_xs) (ms_regs ms1) (ms_mem ms1) MD1
    (ms_regs ms2) (ms_mem ms2) MD2 HI1 HM1 HB1 HJ1
    ltac:(unfold MD2; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
    ltac:(unfold MD2; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
    UN2 HG U20 F49 F50 HRg2 Ka2 Ka3 Ka4) as (HI2 & HM2 & HB2).
  clear HF HFr HG HRg2.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_eq_U, (ck_U0 _ 49 (md_socket_errno mbs) F49 ltac:(lia)), U_lit in Hc by lia.
  * (* socket_errno = 0: on to the send errno *)
    apply Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ1 SHOK tk_span; [te_awr_m U20|].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
    te_kept HFr U20 UN3.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (MD3 := mdq) end.
    te_kr HS (2%bv : bv 5) 2%nat Kb2. te_kr HS (3%bv : bv 5) 3%nat Kb3. te_kr HS (4%bv : bv 5) 4%nat Kb4.
    pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HRg3.
    destruct (te_adv (tk_E c (ms_regs ms1) te_xs) (ms_regs ms2) (ms_mem ms2) MD2
      (ms_regs ms3) (ms_mem ms3) MD3 HI2 HM2 HB2 HJ1
      ltac:(unfold MD3; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
      ltac:(unfold MD3; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
      UN3 HG U20 F49 F50 HRg3
      ltac:(rewrite Kb2; symmetry; exact Ka2) ltac:(rewrite Kb3; symmetry; exact Ka3)
      ltac:(rewrite Kb4; symmetry; exact Ka4)) as (HI3 & HM3 & HB3).
    clear HF HFr HG HRg3.
    psrr_branch_tok RUN BR HS SHOK tk_span;
      rewrite branch_eq_U, (ck_U0 _ 50 (md_send_errno mbs) F50 ltac:(lia)), U_lit in Hc0 by lia.
    -- (* send_errno = 0: the ring test *)
       apply Z.eqb_eq in Hc0.
       assert (HMAIN : tk_main c) by (split; [exact Hc | exact Hc0]).
       paj_run_tok RUN HS HJ1 SHOK tk_span; [te_awr_m U20|].
       lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms4 end.
       te_kept HFr U20 UN4.
       lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (MD4 := mdq) end.
       te_kr HS (2%bv : bv 5) 2%nat Kc2. te_kr HS (3%bv : bv 5) 3%nat Kc3. te_kr HS (4%bv : bv 5) 4%nat Kc4.
       pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HRg4.
       destruct (te_adv (tk_E c (ms_regs ms1) te_xs) (ms_regs ms3) (ms_mem ms3) MD3
         (ms_regs ms4) (ms_mem ms4) MD4 HI3 HM3 HB3 HJ1
         ltac:(unfold MD4; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
         ltac:(unfold MD4; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
         UN4 HG U20 F49 F50 HRg4
         ltac:(rewrite Kc2; symmetry; exact Kb2) ltac:(rewrite Kc3; symmetry; exact Kb3)
         ltac:(rewrite Kc4; symmetry; exact Kb4)) as (HI4 & HM4 & HB4).
       assert (Dbuf : forall i, 0 <= i < tk_len c ->
                 aview SEGS (w_H W) (ms_mem ms4) (tk_r c + i) = aview SEGS (w_H W) memc (tk_r c + i)).
       { intros i Hi. rewrite (UN4 (tk_r c + i)), (UN3 (tk_r c + i)), (UN2 (tk_r c + i));
           try (unfold apart, amem_range, kLowMemEnd, kHighMemBeg, MD_SIZE in *; cbv beta; lia).
         exact (Hbufk i Hi). }
       clear HF HFr HG HRg4.
       psrr_branch_tok RUN BR HS SHOK tk_span;
         rewrite (ck_lt _ (SLit 15) (SOff 51 0) 15 (md_n_req mbs)) in Hc1
           by (first [reflexivity | apply ck_den0; [exact F51 | lia] | lia]).
       ++ (* the ring is full: the chunk-loop set-up *)
          apply Z.ltb_lt in Hc1.
          paj_run_to_tok RUNTO HS HJ1 SHOK tk_span TP_CL0; [te_awr_m U20|].
          lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms5 end.
          te_kept HFr U20 UN5.
          lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (MD5 := mdq) end.
          te_kr HS (2%bv : bv 5) 2%nat Kd2. te_kr HS (3%bv : bv 5) 3%nat Kd3. te_kr HS (4%bv : bv 5) 4%nat Kd4.
          pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HRg5.
          destruct (te_adv (tk_E c (ms_regs ms1) te_xs) (ms_regs ms4) (ms_mem ms4) MD4
            (ms_regs ms5) (ms_mem ms5) MD5 HI4 HM4 HB4 HJ1
            ltac:(unfold MD5; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
            ltac:(unfold MD5; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
            UN5 HG U20 F49 F50 HRg5
            ltac:(rewrite Kd2; symmetry; exact Kc2) ltac:(rewrite Kd3; symmetry; exact Kc3)
            ltac:(rewrite Kd4; symmetry; exact Kc4)) as (HI5 & HM5 & HB5).
          te_kr HS (8%bv : bv 5) 8%nat Z8. te_kr HS (9%bv : bv 5) 9%nat Z9.
          te_kr HS (18%bv : bv 5) 18%nat Z18. te_kr HS (19%bv : bv 5) 19%nat Z19.
          te_kr HS (20%bv : bv 5) 20%nat Z20. te_kr HS (23%bv : bv 5) 23%nat Z23.
          pmkst HS.
          apply (HCL0 (ms_regs ms5) (ms_mem ms5) MD5 HI5).
          ** split; [rewrite Z8; exact (proj1 HR0)|].
             split; [rewrite Z9; exact (proj1 (proj2 HR0)) | rewrite Z23; exact R23].
          ** split; [rewrite Z18; exact (proj1 HRN) | rewrite Z19; exact (proj2 HRN)].
          ** rewrite Z20. exact R20.
          ** exists mbs. split; [exact HM5|]. split; [|reflexivity].
             split; [exact HMW|]. split; [exact Hc|]. split; [exact Hc0|].
             split; [reflexivity|]. split; [reflexivity|]. split.
             --- unfold owe. rewrite md_reqs_length.
                 destruct (Z.ltb_spec (Z.of_nat (Z.to_nat (md_n_req mbs))) NL_SENT_MAX) as [Hq|Hq];
                   [exfalso; unfold NL_SENT_MAX in *; lia | reflexivity].
             --- apply md_n_req_len. exact HMW.
          ** exact HB5.
          ** exact HMAIN.
       ++ (* a free slot: the call of checked_memcpy *)
          apply Z.ltb_ge in Hc1.
          paj_run_tok RUN HS HJ1 SHOK tk_span; [te_awr_m U20|].
          lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms5 end.
          te_kept HFr U20 UN5.
          lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (MD5 := mdq) end.
          te_kr HS (2%bv : bv 5) 2%nat Kd2. te_kr HS (3%bv : bv 5) 3%nat Kd3. te_kr HS (4%bv : bv 5) 4%nat Kd4.
          pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HRg5.
          destruct (te_adv (tk_E c (ms_regs ms1) te_xs) (ms_regs ms4) (ms_mem ms4) MD4
            (ms_regs ms5) (ms_mem ms5) MD5 HI4 HM4 HB4 HJ1
            ltac:(unfold MD5; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
            ltac:(unfold MD5; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
            UN5 HG U20 F49 F50 HRg5
            ltac:(rewrite Kd2; symmetry; exact Kc2) ltac:(rewrite Kd3; symmetry; exact Kc3)
            ltac:(rewrite Kd4; symmetry; exact Kc4)) as (HI5 & HM5 & HB5).
          te_kr HS (8%bv : bv 5) 8%nat Z8. te_kr HS (9%bv : bv 5) 9%nat Z9.
          te_kr HS (18%bv : bv 5) 18%nat Z18. te_kr HS (19%bv : bv 5) 19%nat Z19.
          te_kr HS (20%bv : bv 5) 20%nat Z20. te_kr HS (23%bv : bv 5) 23%nat Z23.
          te_kr HS (21%bv : bv 5) 21%nat Z21. te_kr HS (11%bv : bv 5) 11%nat Z11.
          te_reg HS (1%bv : bv 5) P1. te_reg HS (10%bv : bv 5) P10. te_reg HS (12%bv : bv 5) P12.
          te_reg HS (22%bv : bv 5) P22. te_reg HS (24%bv : bv 5) P24.
          pmkst HS.
          apply (HCP1 (ms_regs ms5) (ms_mem ms5) MD5 HI5).
          ** split; [rewrite Z8; exact (proj1 HR0)|].
             split; [rewrite Z9; exact (proj1 (proj2 HR0)) | rewrite Z23; exact R23].
          ** split; [rewrite Z18; exact (proj1 HRN) | rewrite Z19; exact (proj2 HRN)].
          ** rewrite P1. cbn [sv_denot]. rewrite (img_env_codeptr _ HEI). reflexivity.
          ** rewrite P10. apply (te_den_slot _ (md_n_req mbs));
               [exact E20 | exact F51 | lia | unfold MD_SIZE in *; lia | lia].
          ** rewrite Z11. exact R11.
          ** rewrite P12. apply (ck_den0 _ 21 (tk_len c)); [exact E21 | unfold NL_SENT_LEN in *; lia].
          ** rewrite Z20. exact R20.
          ** rewrite Z21. exact R21.
          ** rewrite P22. apply (ck_denoff _ 20 (tk_m c) 8336); [exact E20 | unfold MD_SIZE in *; lia].
          ** rewrite P24. apply (tk_den_shx _ (SOff 20 8336) (tk_m c + MD_N_REQ));
               [ apply (ck_Uoff _ 20 (tk_m c) 8336); [exact E20 | unfold MD_SIZE in *; lia
                 | unfold MD_N_REQ, MD_SIZE in *; lia]
               | unfold tk_Bx; apply (tk_U_reg c (ms_regs ms1) te_xs 23 23%bv);
                 [lia | reflexivity | exact R23 | unfold SHADOW_OFF; lia]
               | unfold MD_N_REQ, MD_SIZE in *; lia ].
          ** exact HM5.
          ** exact HB5.
          ** exact HMAIN.
          ** lia.
          ** intros i Hi. rewrite (UN5 (tk_r c + i));
               [ exact (Dbuf i Hi)
               | unfold amem_range, kLowMemEnd, kHighMemBeg in *; lia
               | cbv beta; unfold apart, MD_SIZE in *; lia ].
    -- (* send_errno <> 0: 0 at m + 4, then the epilogue *)
       apply Z.eqb_neq in Hc0.
       paj_run_to_tok RUNTO HS HJ1 SHOK tk_span TP_RT; [te_awr_m U20|].
       lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms4 end.
       te_kept HFr U20 UN4.
       lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (MD4 := mdq) end.
       te_kr HS (2%bv : bv 5) 2%nat Kc2. te_kr HS (3%bv : bv 5) 3%nat Kc3. te_kr HS (4%bv : bv 5) 4%nat Kc4.
       te_kr HS (23%bv : bv 5) 23%nat Kc23.
       pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HRg4.
       assert (VZ : val_mem SEGS (rdW W (ms_mem ms4)) (tk_m c + 4) 4 0).
       { eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
           [ exact HRg4 | exact U20 | te_in | reflexivity | te_zrng | te_zrng ]. }
       assert (VO : val_mem SEGS (rdW W (ms_mem ms4)) (tk_m c + 0) 4 (md_socket_errno mbs)).
       { eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
           [ exact HRg4 | exact U20 | te_in | apply ck_den0; [exact F49 | lia] | te_zrng | te_zrng ]. }
       destruct (te_exit_step (ms_regs ms3) (ms_mem ms3) MD3 (ms_regs ms4) (ms_mem ms4) MD4 4 0
         ltac:(right; split; reflexivity) HI3 HM3 HB3 HJ1
         ltac:(unfold MD4; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
         ltac:(unfold MD4; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
         UN4 HG VZ VO
         ltac:(rewrite Kc2; symmetry; exact Kb2) ltac:(rewrite Kc3; symmetry; exact Kb3)
         ltac:(rewrite Kc4; symmetry; exact Kb4)) as (HI4 & HM4 & HB4).
       te_reg HS (11%bv : bv 5) P11.
       pmkst HS.
       destruct (mres_send mbs kbs req HML HMW Hc Hc0) as (HL2 & HRES & HRC & HAT).
       apply (HRET (ms_regs ms4) (ms_mem ms4) MD4 HI4 ltac:(rewrite Kc23; exact R23)).
       intros regs2 H10.
       apply (tk_post_of SK B c HC (ms_mem ms4) (- md_send_errno mbs) no_attrs (md_zero_send mbs)
         HM4 HRES ltac:(symmetry; exact HRC) ltac:(symmetry; exact HAT) HB4 regs2).
       rewrite H10, P11. apply (ck_sub0 _ (SOff 50 0) (md_send_errno mbs));
         [ apply (ck_U0 _ 50 _ F50); lia | lia ].
  * (* socket_errno <> 0: 0 at m, then the epilogue *)
    apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ1 SHOK tk_span TP_RT; [te_awr_m U20|].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
    te_kept HFr U20 UN3.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (MD3 := mdq) end.
    te_kr HS (2%bv : bv 5) 2%nat Kb2. te_kr HS (3%bv : bv 5) 3%nat Kb3. te_kr HS (4%bv : bv 5) 4%nat Kb4.
    te_kr HS (23%bv : bv 5) 23%nat Kb23.
    pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HRg3.
    assert (VZ : val_mem SEGS (rdW W (ms_mem ms3)) (tk_m c + 0) 4 0).
    { eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
        [ exact HRg3 | exact U20 | te_in | reflexivity | te_zrng | te_zrng ]. }
    assert (VO : val_mem SEGS (rdW W (ms_mem ms3)) (tk_m c + 4) 4 (md_send_errno mbs)).
    { eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
        [ exact HRg3 | exact U20 | te_in | apply ck_den0; [exact F50 | lia] | te_zrng | te_zrng ]. }
    destruct (te_exit_step (ms_regs ms2) (ms_mem ms2) MD2 (ms_regs ms3) (ms_mem ms3) MD3 0 4
      ltac:(left; split; reflexivity) HI2 HM2 HB2 HJ1
      ltac:(unfold MD3; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
      ltac:(unfold MD3; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
      UN3 HG VZ VO
      ltac:(rewrite Kb2; symmetry; exact Ka2) ltac:(rewrite Kb3; symmetry; exact Ka3)
      ltac:(rewrite Kb4; symmetry; exact Ka4)) as (HI3 & HM3 & HB3).
    te_reg HS (11%bv : bv 5) P11.
    pmkst HS.
    destruct (mres_sock mbs kbs req HML HMW Hc) as (HL2 & HRES & HRC & HAT).
    apply (HRET (ms_regs ms3) (ms_mem ms3) MD3 HI3 ltac:(rewrite Kb23; exact R23)).
    intros regs2 H10.
    apply (tk_post_of SK B c HC (ms_mem ms3) (- md_socket_errno mbs) no_attrs (md_zero_sock mbs)
      HM3 HRES ltac:(symmetry; exact HRC) ltac:(symmetry; exact HAT) HB3 regs2).
    rewrite H10, P11. apply (ck_sub0 _ (SOff 49 0) (md_socket_errno mbs));
      [ apply (ck_U0 _ 49 _ F49); lia | lia ].
Qed.

End w.

