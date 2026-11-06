(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v, with its module names changed; 419 of its 455 lines of code are new or changed and 273 lines of the source are left out. *)
(* text_of on image A: the end of the copy arm, from THE NUL CUT (+0x24c, after malloc and checked_memcpy) to the
   Post (lib/A/Prog/text_ofDefs.v to_post):
     +0x24c .. +0x25c  a0 := block + k, the 1-byte check of the NUL's address (its shadow entry from the block)
     +0x260            sb zero, 0(a0)
     +0x264 .. +0x268  the 8-byte check of o (s5 = (s0 >> 3) + s4)
     +0x26c            sd s3, 0(s0): *own := the block
     +0x270 .. +0x294  a0 := the block, the seven restores, the pop, ret
   (the token engine, restarted from the cut's machine state: atom 34 names block + k through the alias
   s3 + s1 = atom 34), then the apost: the kept clause of the cut composed with the run's (akept_trans_ly), the fresh
   block dropped (akept_drop_block), the shadow clause by ashadow_kept_AR, the copy arm of text_of_apostA.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YG0p YG08 YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkSide LinkWalkAlloc text_buf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepot.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkNoWrite LinkWalkLeaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c text_ofDefs text_ofKit text_ofMalKit LinkWalkShadow LinkWalkCall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition TO_AT24C : Z := AF_text_of + 0x24c.
(* the bytes the code copies: k bytes of the input from adv *)
Definition to_t (inp : list byte) (adv k : Z) : list byte := firstn (Z.to_nat k) (skipn (Z.to_nat adv) inp).

(* the restart: atoms 0 .. 31 the registers, 32 the shadow base, 34 block + k, 40 .. 46 the seven saves *)
Definition tt_xs (res k : Z) (regs : bvmap 5 word) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 0; Z_to_bv 64 (res + k); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 0; Z_to_bv 64 0] ++ map (fun r => getr regs (Z_to_bv 5 r)) TO_SAVED.
Definition tt_stk : YP09.region := YP09.mkRegion (Some 2%nat) 8 64 0 0
  [YP09.mkChunk 56 (CVal 8 (SOff 40 0)); YP09.mkChunk 48 (CVal 8 (SOff 41 0)); YP09.mkChunk 40 (CVal 8 (SOff 42 0));
   YP09.mkChunk 32 (CVal 8 (SOff 43 0)); YP09.mkChunk 24 (CVal 8 (SOff 44 0)); YP09.mkChunk 16 (CVal 8 (SOff 45 0));
   YP09.mkChunk 8 (CVal 8 (SOff 46 0))].
Definition tt_rN : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 1 [].
Definition tt_rO : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 0 8 [].
Definition tt_alias : sv * sv := (SAlu ALU_ADD (SOff 19 0) (SOff 9 0), SOff 34 0).
Definition tt_ss : sstate := mkSS TO_AT24C sr_atoms [tt_stk; tt_rN; tt_rO] None
  (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (34%nat, mkAF 4096 (2 ^ 47 - 2) 0); (19%nat, mkAF 4096 (2 ^ 47 - 2) 0); (8%nat, mkAF 0 (2 ^ 47 - 9) 0)]
           [] [tt_alias]).
Definition tt_s5 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 20 0).
Definition tt_Bx : sv := SOff 20 0.
Definition tt_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).


(* the shadow address of an atom plus a constant, with the shadow base in atom b *)
Lemma tm_shadow_sv : forall Ev n b k v, bv_unsigned (ew Ev n) = v -> 0 <= v + k < 2 ^ 64 ->
  bv_unsigned (ew Ev b) = SHADOW_OFF ->
  sv_denot Ev (SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff b 0)) = Z_to_bv 64 (SHADOW_OFF + (v + k) / 8).
Proof.
  intros Ev n b k v H Hk Hb.
  rewrite (denot_lit_U Ev (SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff b 0))).
  rewrite U_SAlu, U_SAlu, !U_SOff, U_SLit. cbn [zalu_raw]. rewrite H, Hb. unfold zcanon, M64.
  f_equal. rewrite (Z.mod_small (v + k)) by lia. change (Z.land (3 mod 2 ^ 64) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite Z.add_0_r, (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite (Z.mod_small ((v + k) / 8)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hd : 0 <= (v + k) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small; [lia|]. unfold SHADOW_OFF. lia.
Qed.

Lemma tm_grow : forall (H : word -> bool) (m m' : word -> option byte),
  mem_grows (mrestrict H m) (mrestrict H m') -> forall a, apresent H m a -> apresent H m' a.
Proof.
  intros H m m' HG a (Hh & b & Hb). split; [exact Hh|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh, Hb in HG.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | reflexivity].
Qed.

Lemma tm_nth_firstn_skipn : forall (l : list byte) a k i, (i < k)%nat -> (a + k <= length l)%nat ->
  nth_error (firstn k (skipn a l)) i = nth_error l (a + i).
Proof.
  intros l a k i Hi Hl. rewrite nth_error_firstn. destruct (Nat.ltb_spec i k); [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma tm_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof.
  intros [x1 x2] [y1 y2]. destruct (Z.eq_dec x1 y1), (Z.eq_dec x2 y2);
    [left; congruence | right; congruence | right; congruence | right; congruence].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Lemma tm_ms_eta : forall ms : machine_state, ms_fregs ms = fp_regs -> ms_svc_pending ms = None ->
  ms_resv ms = None -> ms_fcsr ms = fp_csr -> ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).

(* ---- THE NUL CUT (+0x24c): after malloc and the copy, before the NUL ---- *)
Definition to_gi_24c (cx : tocx) (c0 c1 : Z) (inp : list byte) (adv n k res : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (ms : machine_state) (md : Model) : Prop :=
  let regs := to_regs cx in
  let R := ms_regs ms in
  let m := rdW W2 (ms_mem ms) in
  let rd := aview SEGS (w_H W2) (ms_mem ms) in
  let sp := to_sp cx in
  ms_pc_val ms = w64 (BASE + TO_AT24C) /\
  ms_resv ms = None /\ ms_svc_pending ms = None /\ ms_rom ms = seg_rom SEGS /\
  ms_fregs ms = fp_regs /\ ms_fcsr ms = fp_csr /\
  ajournal_gx SEGS B (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx) ly2 S2 W2 (ms_mem ms) md (to_k cx + 1) /\
  m_fds md = m_fds (to_mdc cx) /\ m_fs md = m_fs (to_mdc cx) /\
  getr R 2 = w64 (sp - TO_FRAME) /\ getr R 8 = w64 (to_o cx) /\ getr R 9 = w64 k /\ getr R 19 = w64 res /\
  getr R 20 = w64 SHADOW_OFF /\ getr R 21 = w64 (SHADOW_OFF + to_o cx / 8) /\
  (forall r, In r TO_UNTOUCHED -> getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  (forall j, (j < 7)%nat ->
     rdword rd (sp - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 (nth j TO_SAVED 0))))) /\
  ablocks B ly2 S2 = ablocks B (to_lyc cx) (to_Sc cx) ++ [(res, k + 1)] /\ frames S2 = frames (to_Sc cx) /\
  (forall c q, frame_addr ly2 c q = frame_addr (to_lyc cx) c q) /\ 4096 <= res /\
  akept SEGS B (to_lyc cx) (to_Sc cx) (to_W cx) (to_memc cx) W2 (ms_mem ms) (sp - TEXT_OF_AK) sp
    (fun a => to_E cx a \/ res <= a < res + req_size (k + 1)) /\
  (forall a, sp - TEXT_OF_AK <= a < sp -> apresent (w_H W2) (ms_mem ms) a) /\
  mo_le MT (to_Sc cx) S2 (mo_malloc MT (k + 1)) /\ text_of_ledpost B (to_Sc cx) S2 /\
  to_inp cx c0 c1 inp /\ 1 <= adv <= 3 /\ adv + n <= c1 /\ 0 <= k <= n /\ n <= 319 /\
  ~ In (zb 0) (to_t inp adv k) /\ abytes SEGS m res (to_t inp adv k) /\
  au64_at SEGS m (to_p cx) (c0 + adv + n) /\ au64_at SEGS m (to_p cx + 8) (c1 - adv - n) /\ abuf SEGS m (to_p cx) 16 /\
  (forall i, 0 <= i < 8 -> writable_at SEGS m (to_o cx + i)) /\ range_addressable rd SHADOW_OFF (to_o cx) 8.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis MTL : ameter_laws MT.
Hypothesis TB : AF0m.PcapSyms B.

Lemma to_tail : forall cx c0 c1 inp adv n k res ly2 S2 W2 ms md,
  to_pre SK B MT CTX cx -> to_gi_24c cx c0 c1 inp adv n k res ly2 S2 W2 ms md ->
  SRr SEGS W2 (mkCfg ms md) (to_post SK B MT cx).
Proof.
  intros cx c0 c1 inp adv n k res ly2 S2 W2 ms md HPX HGI.
  pose proof HPX as (HPRE & HRD & Hlive & Hmo & Hch & Hctx & Hled & HP).
  pose proof HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
  destruct (to_pre_happ SK B MT CTX cx HPX) as (AMp & AMo).
  unfold to_gi_24c in HGI. cbv zeta in HGI.
  destruct HGI as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & HJ2 & Hfd & Hfs & R2 & R8 & R9 & R19 & R20 & R21 & RUT & RSV
    & Hbl & Hfrs & Hfa & H4096 & HK & HPW & MLE & HLED & HINP & Hadv & Hadvn & Hkn & Hn319 & HNZ & HBK & Pp & Pp8
    & HBP & HBO & HRAo).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as (HB0' & HB1' & HB2').
  pose proof pa_segs_low as Hsegs.
  pose proof (to_win SK B MT CTX cx HPX) as (Wce & W47 & W16 & Wlo & Whi).
  pose proof (ajournal_gx_row SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hrow & _ & _ & _).
  set (regs := to_regs cx) in *. set (W := to_W cx) in *. set (R := ms_regs ms) in *. set (sp := to_sp cx) in *.
  set (p := to_p cx) in *. set (o := to_o cx) in *.
  assert (Esp : sp = spZ regs) by reflexivity.
  assert (HKv : TEXT_OF_AK = 16448) by reflexivity.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (HinP : In (res, k + 1) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res (k + 1) HAR2 HinP) as (_ & _ & Hbc & _ & HpoB & _ & _).
  assert (Hrq : req_size (k + 1) = k + 1)
    by (unfold req_size; replace (k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
  rewrite Hrq in Hbc, HpoB.
  (* the write set's bytes are no bytes of the block *)
  assert (EnF : forall a, to_E cx a -> ~ (res <= a < res + (k + 1))).
  { intros a Ha. rewrite <- Hrq. apply (to_fresh_not_sclass SEGS B LAWS (to_lyc cx) (to_Sc cx) ly2 S2 W2 _ md res (k + 1)
      a HAR2 Hbl Hfrs Hfa Hrow).
    eapply (sclass_of_ajw SK SEGS B LAWS); [exact HGok | exact HJ | exact (Hajw a Ha) |].
    destruct (to_E_app cx a (conj AMp AMo) Ha) as [H | H]; [left; exact H | right; lia]. }
  (* ---- the restart at +0x24c ---- *)
  assert (Hms : ms = mkst R (Z_to_bv 64 (BASE + TO_AT24C)) (ms_mem ms) (seg_rom SEGS))
    by (rewrite (tm_ms_eta ms Hfr Hsv Hrv Hfc) at 1; rewrite Hpc, Hrom; reflexivity).
  set (xs := tt_xs res k regs).
  remember (Eimg (Ereg R xs)) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (ER2 : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat -> ew E2 n = getr R r)
    by (intros n0 r Hr Hn; subst E2; rewrite Eimg_low by exact Hn; exact (ew_Ereg_nat _ _ n0 r Hr)).
  assert (EX2 : forall j, (j < 15)%nat -> ew E2 (32 + j) = nth j xs (Z_to_bv 64 0))
    by (intros j Hj; subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ xs j)).
  assert (HRO2 : regs_ok E2 sr_atoms R) by (subst E2; apply regs_ok_Eimg_Ereg).
  clear HE2.
  assert (Hsp' : 0 <= sp - 64 < 2 ^ 64) by lia.
  assert (Ho0 : 0 <= o < 2 ^ 64) by (unfold o, to_o, aarg, argZ; apply u64_range).
  assert (Hp0 : 0 <= p < 2 ^ 64) by (unfold p, to_p, aarg, argZ; apply u64_range).
  assert (Ho64 : 0 <= o /\ o + 8 <= 2 ^ 47 - 1) by (unfold amem_range in AMo; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (U2 : bv_unsigned (ew E2 2) = sp - 64).
  { rewrite (ER2 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)), R2. unfold TO_FRAME. apply unsigned_lit_small. lia. }
  assert (E8 : ew E2 8 = Z_to_bv 64 o) by (rewrite (ER2 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia)); exact R8).
  assert (U8 : bv_unsigned (ew E2 8) = o) by (rewrite E8; apply unsigned_lit_small; lia).
  assert (E9 : ew E2 9 = Z_to_bv 64 k) by (rewrite (ER2 9%nat 9%bv eq_refl ltac:(unfold A_TEXT; lia)); exact R9).
  assert (U9 : bv_unsigned (ew E2 9) = k) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (E19 : ew E2 19 = Z_to_bv 64 res) by (rewrite (ER2 19%nat 19%bv eq_refl ltac:(unfold A_TEXT; lia)); exact R19).
  assert (U19 : bv_unsigned (ew E2 19) = res) by (rewrite E19; apply unsigned_lit_small; lia).
  assert (E20 : ew E2 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER2 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia)); exact R20).
  assert (U20 : bv_unsigned (ew E2 20) = SHADOW_OFF) by (rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (E34 : ew E2 34 = Z_to_bv 64 (res + k)) by exact (EX2 2%nat ltac:(lia)).
  assert (U34 : bv_unsigned (ew E2 34) = res + k) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (CH : forall (j : nat) off, (j < 7)%nat -> off = 56 - 8 * Z.of_nat j ->
            YP09.chunk_ok SEGS E2 (mrestrict (w_H W2) (ms_mem ms)) (sp - 64)
              (YP09.mkChunk off (CVal 8 (SOff (40 + j) 0)))).
  { intros j off Hj Hoff.
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth j TO_SAVED 0)))) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr.
    apply (chunk_ok_val SEGS E2 _ (sp - 64) off 8 (SOff (40 + j) 0)
             (bv_unsigned (getr regs (Z_to_bv 5 (nth j TO_SAVED 0))))).
    - cbn [sv_denot]. replace (40 + j)%nat with (32 + (8 + j))%nat by lia.
      rewrite (EX2 (8 + j)%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite Z_to_bv_bv_unsigned.
      destruct j as [|[|[|[|[|[|[|j]]]]]]]; [reflexivity.. | lia].
    - change (8 * Z.of_N 8) with 64. exact Hr.
    - cbn. lia.
    - apply (val_mem_of_rdword SEGS).
      replace (sp - 64 + off) with (sp - 8 - 8 * Z.of_nat j) by lia. exact (RSV j Hj). }
  (* the NUL's byte is a byte of the block: present, writable, addressable *)
  assert (HNP : apresent (w_H W2) (ms_mem ms) (res + k)) by (apply HpoB; lia).
  assert (HoW : forall i, 0 <= i < 8 -> writable_at SEGS (rdW W2 (ms_mem ms)) (o + i)) by exact HBO.
  assert (HoE : forall i, 0 <= i < 8 -> to_E cx (o + i)).
  { intros i Hi. exists (o, o + 8). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
  assert (HpE : forall i, 0 <= i < 16 -> to_E cx (p + i)).
  { intros i Hi. exists (p, p + 16). split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (HoN : forall i, 0 <= i < 8 -> o + i <> res + k).
  { intros i Hi E. apply (EnF (o + i) (HoE i Hi)). lia. }
  assert (HpN : forall i, 0 <= i < 16 -> p + i <> res + k).
  { intros i Hi E. apply (EnF (p + i) (HpE i Hi)). lia. }
  pose proof (to_pre_P SK B MT CTX cx HPX) as HP0.
  destruct HP0 as (c0' & c1' & inp' & _ & _ & _ & _ & _ & Hp8 & _ & _ & HAFp & _ & _ & _ & _ & HAFo & HAPop & _).
  assert (HopA : o + 8 <= p \/ p + 16 <= o)
    by (revert HAPop; unfold apart, o, p, to_o, to_p, regs; clear; intros; lia).
  assert (Hp64 : p + 16 <= 2 ^ 47) by (unfold amem_range in AMp; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (HoS : o + 8 <= sp - TEXT_OF_AK \/ sp <= o)
    by (revert HAFo; unfold apart_frame, o, sp, to_o, to_sp, regs; clear; intros; lia).
  assert (HS5 : st_ok_pi SEGS VAL E2 tt_ss
      (restrict (w_H W2) (mkst R (Z_to_bv 64 (BASE + TO_AT24C)) (ms_mem ms) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - exact HRO2.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
        unfold region_ok, tt_stk, tt_rN, tt_rO;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U2, ?U34, ?U8.
      + split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * exact (CH 0%nat 56 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 1%nat 48 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 2%nat 40 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 3%nat 32 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 4%nat 24 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 5%nat 16 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 6%nat 8 ltac:(lia) ltac:(reflexivity)).
      + split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o' Ho'. replace (res + k + o') with (res + k) by lia. apply (apresent_writable SEGS). exact HNP.
      + split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o' Ho'. exact (HoW o' Ho').
    - apply pairwise_disjoint_of_extents. unfold tt_stk, tt_rN, tt_rO, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U34, U8.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      assert (Hon : o + 8 <= res + k \/ res + k + 1 <= o).
      { destruct (Z_lt_le_dec (res + k) o) as [H | H]; [right; lia|].
        destruct (Z_lt_le_dec (res + k) (o + 8)) as [H' | H']; [|left; lia].
        exfalso. apply (HoN (res + k - o) ltac:(lia)). lia. }
      repeat split; lia.
    - split; [|split; [exact I|]].
      + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U2, U20, U34, U19, U8. rewrite Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16.
        repeat split; lia.
      + cbn [f_alias alias_ok tt_alias]. split; [|exact I].
        rewrite (denot_lit_U E2 (SAlu ALU_ADD (SOff 19 0) (SOff 9 0))), (denot_lit_U E2 (SOff 34 0)).
        rewrite U_SAlu, !U_SOff. cbn [zalu_raw]. rewrite U19, U9, U34. unfold zcanon, M64. rewrite !Z.add_0_r.
        f_equal. rewrite <- Z.add_mod by lia. reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E2 _ _ (21%bv : bv 5) tt_s5 HS5 ltac:(vm_compute; reflexivity)
    ltac:(unfold tt_s5; cbn [ms_regs restrict mkst]; rewrite (tm_shadow_sv E2 8 20 0 o U8 ltac:(lia) U20), Z.add_0_r;
          exact (eq_sym R21))) as HS6.
  clear HS5.
  assert (SHOK : sh_ok SEGS tt_Bx [mkSHE 34 0 1; mkSHE 8 0 8] E2 (mrestrict (w_H W2) (ms_mem ms))).
  { pose proof (amem_range_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms) md res (k + 1) (res + k) 1 HAR2 HinP
      ltac:(lia) ltac:(rewrite Hrq; lia)) as AMN.
    pose proof (range_addressable_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms) md res (k + 1) (res + k) 1 HAR2 HinP
      ltac:(lia) ltac:(rewrite Hrq; lia)) as RAN.
    assert (HB : U E2 tt_Bx = SHADOW_OFF)
      by (unfold tt_Bx; rewrite (U_atom E2 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia); reflexivity).
    unfold sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; rewrite HB.
    - rewrite (U_atom E2 34 (res + k) E34) by lia. split.
      + rewrite Z.add_0_r, Z.sub_0_r, <- (aview_rd_of SEGS). exact RAN.
      + intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. unfold amem_range in AMN.
        unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
    - rewrite (U_atom E2 8 o E8) by lia. split.
      + rewrite Z.add_0_r, Z.sub_0_r, <- (aview_rd_of SEGS). exact HRAo.
      + intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. unfold amem_range in AMo.
        unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
  (* the block is no block of the call's state *)
  assert (HnotSc : ~ In (res, k + 1) (ablocks B (to_lyc cx) (to_Sc cx))).
  { intros Hin. apply in_split in Hin as (l1 & l2 & El).
    pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 _ md (res, k + 1) (res, k + 1) l1 l2 [] HAR2
      ltac:(rewrite Hbl, El, <- app_assoc; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. lia. }
  pose proof HJ as (_ & _ & (memSA2 & HJAi2 & _) & _).
  pose proof HJAi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
  assert (Hbl2 : forall b m0, In (b, m0) (ablocks B (to_lyc cx) (to_Sc cx)) -> In (b, m0) (ablocks B ly2 S2))
    by (intros b m0 Hb; rewrite Hbl; apply in_or_app; left; exact Hb).
  rewrite Hms.
  pose (RUN := paj_run_x SK B LAWS (to_G cx) HGok (to_XO cx) (to_OUT cx)).
  paj_run_tok RUN HS6 HJ2 SHOK tt_span.
  { cbn [ss_mem tt_ss]. unfold tt_stk, tt_rN, tt_rO.
    apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    - cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha. rewrite U34 in Ha. left. split; [|lia].
      unfold awr_byte. right.
      destruct (in_dec tm_dec (res, k + 1) (ablocks B (to_ly cx) (to_S cx))) as [Hin0|Hin0].
      + left. split.
        * replace a with (res + (a - res)) by lia. apply (Hgone res (k + 1) (a - res) Hin0 HnotSc). rewrite Hrq. lia.
        * exists res, (k + 1). split; [exact HinP | rewrite Hrq; lia].
      + right. left. exists res, (k + 1). split; [exact HinP|]. split; [exact Hin0 | rewrite Hrq; lia].
    - cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha. rewrite U8 in Ha.
      exact (ajw_mono B _ _ _ _ _ _ _ _ (to_lyc cx) (to_Sc cx) (to_own cx) ly2 S2 (to_own cx) a
        (Hajw a ltac:(replace a with (o + (a - o)) by lia; apply HoE; lia)) Hbl2 (fun x Hx => Hx) Hfa). }
  lazymatch type of HS6 with st_ok_pi _ _ ?Ef _ (restrict _ ?msF) =>
    set (ms6 := msF) in *;
    assert (O6 : forall n0, (n0 < 512)%nat -> ew Ef n0 = ew E2 n0)
      by (intros n0 Hn0; rewrite ?ew_ewset_other by lia; reflexivity);
    set (E6 := Ef) in *
  end.
  prreg HS6 (1%bv : bv 5) T1. prreg HS6 (10%bv : bv 5) T10.
  assert (T1' : getr (ms_regs ms6) 1 = getr regs 1) by (rewrite T1; rewrite O6 by lia; exact (EX2 8%nat ltac:(lia))).
  assert (T10' : getr (ms_regs ms6) 10 = w64 res) by (rewrite T10; rewrite O6 by lia; exact E19).
  clear T1 T10.
  (* the callee-saved registers: the seven restores and the untouched ones *)
  assert (KEEP : aregs_preserved regs (ms_regs ms6)).
  { intros rr Hr. unfold acallee_saved in Hr.
    assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
                 rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    clear Hr.
    assert (UT : forall c : nat, In (Z.of_nat c) TO_UNTOUCHED -> (c < 32)%nat ->
              ew E2 c = getr regs (Z_to_bv 5 (Z.of_nat c))).
    { intros c Hin Hc32.
      rewrite (ER2 c (Z_to_bv 5 (Z.of_nat c)) ltac:(rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
                 change (2 ^ Z.of_N 5) with 32; symmetry; apply Z.mod_small; lia) ltac:(unfold A_TEXT; lia)).
      exact (RUT _ Hin). }
    repeat (destruct Hc as [Hc | Hc]; [subst rr;
      lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
        let Q := fresh "Q" in prreg HS6 (Z_to_bv 5 c) Q; rewrite Q; try rewrite O6 by lia;
        first [ exact (UT 3%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia))
              | exact (UT 4%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia))
              | exact (UT 22%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia))
              | exact (UT 23%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia))
              | exact (UT 24%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia))
              | exact (UT 25%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia))
              | exact (UT 26%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia))
              | first [ exact (EX2 9%nat ltac:(lia)) | exact (EX2 10%nat ltac:(lia))
                      | exact (EX2 11%nat ltac:(lia)) | exact (EX2 12%nat ltac:(lia))
                      | exact (EX2 13%nat ltac:(lia)) | exact (EX2 14%nat ltac:(lia)) ]
              | rewrite U2; replace (sp - 64 + 64) with (spZ regs) by lia;
                unfold spZ; apply Z_to_bv_bv_unsigned ]
      end |]).
    subst rr. prreg HS6 (Z_to_bv 5 27) Q. rewrite Q. try rewrite O6 by lia.
    exact (UT 27%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia)). }
  (* what the run wrote: the NUL at block + k and the block at o *)
  spregion HS6 1%nat HRN. spregion HS6 2%nat HRO.
  assert (VN : val_mem SEGS (rdW W2 (ms_mem ms6)) (res + k + 0) 1 0).
  { refine (field_of_region (segs := SEGS) E6 _ 34 (res + k) _ _ _ _ _ 0 1%N (SLit 0) 0 HRN _ _ _ _ _).
    - rewrite O6 by lia. exact U34.
    - cbn [In]. tauto.
    - reflexivity.
    - cbn. lia.
    - cbn. lia. }
  assert (VO : val_mem SEGS (rdW W2 (ms_mem ms6)) (o + 0) 8 res).
  { refine (field_of_region (segs := SEGS) E6 _ 8 o _ _ _ _ _ 0 8%N (SOff 19 0) res HRO _ _ _ _ _).
    - rewrite O6 by lia. exact U8.
    - cbn [In]. tauto.
    - cbn [sv_denot]. rewrite O6 by lia. rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - cbn. lia.
    - cbn. lia. }
  rewrite Z.add_0_r in VN, VO.
  (* the bytes the run kept *)
  set (Zs := fun a => a = res + k \/ o <= a < o + 8).
  pose proof (kept_of_frame (segs := SEGS) _ _ (w_H W2) (ms_mem ms) (ms_mem ms6) Zs HFr
    ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                  rewrite ?O6 in Hrr by lia; rewrite ?U34, ?U8, ?U2 in Hrr; unfold Zs; lia |]);
          destruct Hin)) as UNk.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR6.
  eapply (paj_ret_at (PL := PL_link) (PI := PI) W2 _ _ _ _ _ HS6 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  rewrite T1'. unfold YK0s.ret_ok in Hraw. rewrite Hraw.
  set (EF := fun a => to_E cx a \/ res <= a < res + req_size (k + 1)).
  assert (KC : akept SEGS B ly2 S2 W2 (ms_mem ms) W2 (ms_mem ms6) (sp - TEXT_OF_AK) sp EF).
  { apply (akept_run SEGS B LAWS pa_segs_low ly2 S2 W2 (ms_mem ms) md W2 (ms_mem ms6) (sp - TEXT_OF_AK) sp EF HAR2);
      [lia | lia | | | ].
    - intros a Ha Hw HnE. apply UNk; [exact Ha|]. unfold Zs. intros [Hq | Hq]; apply HnE; unfold EF.
      + right. rewrite Hrq. lia.
      + left. replace a with (o + (a - o)) by lia. apply HoE. lia.
    - intros a Hpa. exact (tm_grow _ _ _ HG a Hpa).
    - intros a Ha. apply (tm_grow _ _ _ HG). exact (HPW a Ha). }
  assert (KF : akept SEGS B (to_lyc cx) (to_Sc cx) W (to_memc cx) W2 (ms_mem ms6) (sp - TEXT_OF_AK) sp EF).
  { apply (akept_trans_ly SK SEGS B LAWS pa_segs_low (to_lyc cx) (to_Sc cx) W (to_memc cx) ly2 S2 W2 (ms_mem ms)
      W2 (ms_mem ms6) (sp - TEXT_OF_AK) sp (sp - TEXT_OF_AK) sp EF EF EF);
      [lia | lia | exact HK | exact KC | lia | lia | exact Hbl2 | intros f Hf; rewrite Hfrs; exact Hf | exact Hfa
      | tauto | tauto]. }
  pose proof (akept_drop_block SK SEGS B LAWS pa_segs_low (to_lyc cx) (to_Sc cx) W (to_memc cx) W2 (ms_mem ms6)
    (sp - TEXT_OF_AK) sp (to_E cx) ly2 S2 W2 (ms_mem ms6) _ res (k + 1) HAR6 Hbl Hfrs Hfa KF) as KD.
  unfold to_post, apost.
  eexists ly2, S2, (ms_regs ms6), (ms_mem ms6), _.
  split; [reflexivity|].
  split.
  { first [ exact HJ2 | (repeat rewrite wvb_collapse in HJ2); exact HJ2
          | apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low);
            first [exact HJ2 | (repeat rewrite wvb_collapse in HJ2); exact HJ2] ]. }
  split; [exact KEEP|].
  split; [exact Hfrs|].
  split; [repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfd|].
  split; [repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfs|].
  split; [exact KD|].
  split; [exact (ashadow_kept_AR SK SEGS B LAWS pa_segs_low (to_lyc cx) (to_Sc cx) ly2 S2 W (to_memc cx) (to_mdc cx)
                   W2 (ms_mem ms6) _ HARc HAR6)|].
  split.
  { apply (mo_le_mono MT MTL _ _ (mo_malloc MT (k + 1))); [exact MLE|].
    apply (mo_malloc_mono MT MTL). unfold TEXT_OF_LIVE. lia. }
  split; [exact HLED|].
  (* the copy arm of the Post *)
  destruct HINP as (Ic0 & Ic1 & Ic0r & Ic1r & Iinp & Ilen).
  unfold text_of_apostA. intros cc0 cc1 Hcc0 Hcc1 Hr0 Hr1.
  assert (E0 : cc0 = c0) by exact (tm_au64_det SEGS (to_m0 cx) p cc0 c0 Hcc0 Ic0 Hr0 Ic0r).
  assert (E1 : cc1 = c1) by exact (tm_au64_det SEGS (to_m0 cx) (p + 8) cc1 c1 Hcc1 Ic1 Hr1 Ic1r).
  subst cc0 cc1.
  assert (Ht : Z.of_nat (length (to_t inp adv k)) = k).
  { unfold to_t. rewrite length_firstn, length_skipn. lia. }
  (* a byte the run did not write, as it was at the cut *)
  assert (KB6 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a ->
            mbyte SEGS (rdW W2 (ms_mem ms6)) a = mbyte SEGS (rdW W2 (ms_mem ms)) a).
  { intros a Ha HZ. apply (mbyte_of_aview SEGS). exact (UNk a Ha HZ). }
  exists res, res, (to_t inp adv k).
  split; [exact T10'|]. split; [lia|].
  split.
  { split; [|exact HNZ]. destruct HBK as (Hb0 & Hb1 & Hb2).
    split; [lia|]. split; [rewrite length_app; cbn [length]; lia|].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length (to_t inp adv k))) as [Hl | Hl].
    - rewrite nth_error_app1 by exact Hl. rewrite KB6; [exact (Hb2 i Hl) | lia |].
      unfold Zs. intros [Hq | Hq]; [lia|].
      apply (EnF (o + (res + Z.of_nat i - o)) (HoE (res + Z.of_nat i - o) ltac:(lia))). lia.
    - assert (Hik : i = length (to_t inp adv k)) by lia. subst i.
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. cbn [nth_error].
      rewrite Ht. pose proof (VN 0%nat ltac:(lia)) as V. rewrite Z.add_0_r in V. rewrite V. reflexivity. }
  split; [lia|].
  split; [exact VO|]. split; [lia|].
  split.
  { exists (adv + n). split; [lia|].
    assert (KP : forall x, p <= x < p + 16 -> mbyte SEGS (rdW W2 (ms_mem ms6)) x = mbyte SEGS (rdW W2 (ms_mem ms)) x).
    { intros x Hx. apply KB6; [lia|]. unfold Zs. intros [Hq | Hq].
      - apply (HpN (x - p) ltac:(lia)). lia.
      - lia. }
    split.
    { replace (c0 + (adv + n)) with (c0 + adv + n) by lia.
      apply (tm_val_mem_move SEGS _ _ p 8 _ Pp). intros x Hx. apply KP. change (Z.of_nat 8) with 8 in Hx. lia. }
    split.
    { replace (c1 - (adv + n)) with (c1 - adv - n) by lia.
      apply (tm_val_mem_move SEGS _ _ (p + 8) 8 _ Pp8). intros x Hx. apply KP. change (Z.of_nat 8) with 8 in Hx. lia. }
    destruct HBP as (junk & Hl & (Hjb & Hjw)). exists junk. split; [exact Hl|]. split.
    - apply (tm_abytes_move SEGS _ _ p junk Hjb). intros x Hx. apply KP. lia.
    - intros i Hi. apply (writable_kept (segs := SEGS) (w_H W2) (ms_mem ms) (ms_mem ms6) (p + i)
        (tm_grow _ _ _ HG (p + i))). exact (Hjw i Hi). }
  split; [intros H0; lia|].
  intros _. split; [reflexivity|]. split; [lia|].
  exists (k + 1). split; [unfold TEXT_OF_LIVE; lia|]. split; [lia|]. exact Hbl.
Qed.

End b.
End a.
