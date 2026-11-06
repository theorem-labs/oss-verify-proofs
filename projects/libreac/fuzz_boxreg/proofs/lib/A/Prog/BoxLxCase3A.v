(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryUnset.v, with its module paths and module names changed; 2249 of its 2361 lines of code are new or changed and 693 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxCase3.v, with its addresses changed; 555 of its 666 lines of code are new or changed and 2250 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput's case op & 3 = 3 (fuzz_boxreg.c, the rename turn) on the ASan build, segment A: from the
   case cut GI_T 3 (0x803fc, BoxLxDefs.v) to the return slot of read_name (0x80584, pc offset 0x638), where c3_segB
   (BoxLxCase3.v) starts. The code is fuzz_u8 inlined, then read_name (&in):
     0x803fc  ld a1, 0x90(s1); beqz a1 -> 0x80578               n, the input bytes left at the cursor
     0x80404  ld a0, 0x88(s1); the shadow test of p (srli; add s2; lb), the stores of p + 1 and n - 1;
              bnez -> 0x80d5c (the slow path into the report call at 0x80fbc); lbu s5, 0(a0); j 0x8057c
     0x80578  mv s5, zero                                         (no byte left: the index byte is 0)
     0x8057c  addi a0, s1, 0x88; jal read_name                    (ReadName.v tread_name_spec)
   The walk is split on the bytes left at the cursor (none, or at least one). With a byte left, the byte at the
   cursor is a read-only chunk of the input block and the shadow test leaves range_addressable (p + pos) 1, which the
   caller's input block gives (range_addressable_of_block), so the slow path is not taken. The cursor window
   [sp1 + 0x88, sp1 + 0x98) is the only writable window of the runs. The rest of the turn is c3_segB's statement,
   taken here as a premise. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YImgTop YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase YC1g YC1h YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
BoxCJ BoxRo BoxFrame BoxTailVis ReacBoxregInit ReacBoxregSetName ReadName BoxLxDefs BoxLxCase3.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg BoxregUpd printf_facts_c read_name_c LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_rn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the name read_name returns, as the C string set_name gets: its bytes up to the first NUL ---- *)
Lemma c3a_nm : forall (l : list byte) j,
  (j <= length (LLVMFuzzerTestOneInput_rn.nm_str (l ++ [Z_to_bv 8 0])))%nat ->
  bv_unsigned (nth j (l ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) =
  nth j (LLVMFuzzerTestOneInput_rn.nm_str (l ++ [Z_to_bv 8 0]) ++ [0]) 0.
Proof.
  induction l as [|x l IH]; intros j Hj.
  - vm_compute in Hj. assert (j = 0)%nat by lia. subst j. vm_compute. reflexivity.
  - revert Hj. cbn [app LLVMFuzzerTestOneInput_rn.nm_str].
    destruct (Z.eqb_spec (bv_unsigned x) 0) as [Ex | Ex]; intros Hj.
    + cbn [length] in Hj. assert (j = 0)%nat by lia. subst j. cbn [nth app]. exact Ex.
    + destruct j as [|j]; [reflexivity|]. cbn [length] in Hj. cbn [nth app]. apply IH. lia.
Qed.

Lemma c3a_nm_len : forall l : list byte,
  (length (LLVMFuzzerTestOneInput_rn.nm_str (l ++ [Z_to_bv 8 0])) <= length l)%nat.
Proof.
  induction l as [|x l IH].
  - vm_compute. lia.
  - cbn [app LLVMFuzzerTestOneInput_rn.nm_str]. destruct (bv_unsigned x =? 0); cbn [length]; lia.
Qed.

Lemma c3a_bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof.
  intros l1 l2. induction l1 as [|x l IH].
  - change ([] ++ l2) with l2. change (bsum []) with 0. lia.
  - change ((x :: l) ++ l2) with (x :: (l ++ l2)). change (bsum (x :: (l ++ l2))) with (snd x + bsum (l ++ l2)).
    change (bsum (x :: l)) with (snd x + bsum l). rewrite IH. lia.
Qed.

(* ---- the engine's start: the cursor window [0x88, 0x98) of the spill area (atom 9 = s1 = sp1), with p at 0x88
   (atom 32) and n at 0x90 (a closed numeral or atom 33); the input byte at the cursor (atom 34), read-only ---- *)
Definition C3A_Rsl (v90 : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x88 0x98 0x88 0x98
    [YP09.mkChunk 0x88 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x90 (CVal 8 v90)].
Definition C3A_Rin : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
(* sp1 lies above the shadow span (2^46 <= alloc_ceiling <= sp1); s2 = SHADOW_OFF. *)
Definition C3A_F (ex : list (nat * afact)) : facts :=
  mkFacts ((9%nat, mkAF (2 ^ 46) (2 ^ 47) 5) :: (18%nat, mkAF 0x7fff8000 0x7fff8000 0) :: ex) [] [].
(* The registers the walk to the call keeps (it writes a0 .. a3, s5 and ra only). *)
Definition c3a_kl : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 22%bv; 24%bv; 25%bv; 26%bv].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

Lemma c3a_val_mem1 : forall (W : world SEGS) (m : word -> option byte) a v,
  aview SEGS (w_H W) m a = Some v -> val_mem SEGS (mrestrict (w_H W) m) a 1 v /\ 0 <= v < 256.
Proof.
  intros W m a v Hv. destruct (aview_byte SEGS (w_H W) m a v Hv) as (b & Hb & -> & Hr).
  split; [|exact Hr]. intros kk Hk. assert (kk = 0)%nat by lia. subst kk. cbn [Z.of_nat].
  rewrite Z.add_0_r, Hb. f_equal. apply bv_eq. rewrite le_byte_small by (cbn [Z.of_nat]; lia).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.shiftr_div_pow2 by lia. cbn [Z.of_nat Z.mul]. rewrite Z.div_1_r. symmetry. apply Z.mod_small. exact Hr.
Qed.

Lemma c3a_keep_outside : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs m m' H a HF Ha Hn. unfold aview, YP09.mbyte, mrestrict.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis TREADNAME : tread_name_spec B MT.
Hypothesis HRNTR : In [pc_malloc_ra0 (as_code B); A_read_name_mallocRA] (as_universe B).

Section d.
Variable cx : bcx.
Variable fp : Z.

Section e.
Variable POST : bcx -> world SEGS -> config -> Prop.
Variable i : Z.
Hypothesis HB : gb_base B MT cx.

(* The rest of the turn from 0x638 (c3_segB's premises, as BoxLxCase3Top.v's C3SEGA states them). *)
Definition c3a_K : Prop :=
  forall ly' S' W' (ms' : machine_state) md' k' acc' r bs idxb pos nm szn op sstr,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' (ms_mem ms') md' k' ->
  frames S' = [(GB_CID, fp)] -> mo_le MT (c_S cx) S' acc' ->
  0 <= i < 64 -> k' <= 2 + 2 * i -> acc' + mo_free MT <= GB_A MT (i + 1) ->
  ms_pc_val ms' = w64 (BASE + 0x638) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx fp ms' ->
  getr (ms_regs ms') 10 = w64 nm -> getr (ms_regs ms') 20 = w64 r ->
  getr (ms_regs ms') 21 = Z_to_bv 64 idxb -> getr (ms_regs ms') 22 = w64 op ->
  getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) -> getr (ms_regs ms') 26 = w64 (Boxreg.bx_n bs) ->
  0 <= idxb < 256 -> 0 <= op < 256 ->
  c3_M0 cx fp W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') ->
  gcursor cx W' ms' pos ->
  greg B ly' S' W' ms' r bs ->
  ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (nm, szn)] ->
  0 < szn <= 48 ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S')) ->
  Boxreg.boxreg_inv bs ->
  Forall (fun c => 0 < c < 256) sstr -> Z.of_nat (length sstr) + 1 <= szn ->
  (forall j, 0 <= j <= Z.of_nat (length sstr) ->
     aview SEGS (w_H W') (ms_mem ms') (nm + j) = Some (nth (Z.to_nat j) (sstr ++ [0]) 0)) ->
  SRr SEGS W' (mkCfg ms' md') (POST cx).

(* The bytes the phase's facts speak about are none of the cursor's. *)
Lemma c3a_at_cur : forall ly' S' W' mem' md' k' a,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly' S' W' mem' md' k' ->
  frames S' = [(GB_CID, fp)] -> c3_at0 cx fp a ->
  0 <= a < 2 ^ 64 /\ ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98).
Proof.
  intros ly' S' W' mem' md' k' a HJ HFR Ha.
  pose proof (c3_geo B MT LAWS cx fp ly' S' W' mem' md' k' HB HJ HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF8 : 0 <= gF cx fp / 8 < 2 ^ 44) by
    (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold c3_at0 in Ha. unfold gSH, shadow_of_addr, SHADOW_OFF, GB_STK in *. lia.
Qed.

(* ---- the call of read_name (0x80580) and the landing at its return slot 0x80584 ---- *)
Lemma c3a_call : forall k acc ly3 S3 W3 md (regs : bvmap 5 word) mem r bs pos1 op idxb,
  c3a_K ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  0 <= i < 64 -> k <= 1 + 2 * i -> acc <= GB_A MT i ->
  gblk1 B cx ly3 S3 r -> length bs = 288%nat ->
  (forall j, 0 <= j < REG_SIZE ->
     aview SEGS (w_H W3) mem (r + j) = Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_inv bs -> 0 <= op < 256 -> 0 <= idxb < 256 ->
  c3_M0 cx fp W3 r (Boxreg.bx_fabric bs) i bs mem ->
  0 <= pos1 <= c_n cx ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 0x88) = Some (c_p cx + pos1) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 0x90) = Some (c_n cx - pos1) ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 24 = w64 (gSH cx fp) ->
  getr regs 1 = w64 (BASE + 0x638) -> getr regs 10 = w64 (c_sp1 cx + 0x88) ->
  getr regs 20 = w64 r -> getr regs 21 = Z_to_bv 64 idxb -> getr regs 22 = w64 op ->
  getr regs 25 = w64 (Boxreg.bx_fabric bs) -> getr regs 26 = w64 (Boxreg.bx_n bs) ->
  SRr SEGS W3 (cfg_at SEGS A_read_nameP regs mem md) (POST cx).
Proof.
  intros k acc ly3 S3 W3 md regs mem r bs pos1 op idxb HK HJ HFR HMO Hi Hk Hacc HBLK Hlen HR Hinv Hop Hidx HM
    Hpos C88 C90 G2 G8 G9 G3 G4 G18 G24 R1 R10 R20 R21 R22 R25 R26.
  pose proof (c3_geo B MT LAWS cx fp ly3 S3 W3 mem md k HB HJ HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as HBok. pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
  pose proof HB as (HPRE0 & _ & _ & Hinp & _ & _ & Hev & Hlive & _ & _ & _ & _ & _ & HMOK & _ & HNEED).
  pose proof HPRE0 as (HAR0 & _ & _ & Hgp & Htp & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & _).
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & HPRES & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  set (pl := skipn (Z.to_nat pos1) (c_pl cx)).
  assert (Lpl : Z.of_nat (length pl) = c_n cx - pos1) by (subst pl; rewrite length_skipn; unfold c_n in *; lia).
  pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range pl) as (Hrk & Hrk2).
  assert (Usp : spZ regs = c_sp1 cx)
    by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; unfold GB_STK in *; lia).
  unfold gblk1 in HBLK.
  assert (HrIn3 : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HrIn3) as (_ & Hr4096 & Hrceil & _).
  change (req_size REG_SIZE) with 288 in Hrceil.
  assert (Hinp3 : c_n cx = 0 \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B ly3 S3) /\
    4096 <= c_p cx /\ c_p cx + req_size (c_n cx) <= alloc_ceiling /\ in_app (c_p cx) (req_size (c_n cx)))).
  { destruct Hinp as [(Hn0 & _) | (Hn & Hin)]; [left; exact Hn0 | right].
    assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (rewrite HBLK; apply in_or_app; left; exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & Happ & _).
    split; [lia|]. split; [exact Hin3|]. split; [lia|]. split; [lia|]. exact Happ. }
  pose proof HM as (_ & _ & _ & HIN & _).
  eapply SRr_bind.
  { apply (TREADNAME GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)]
      ly3 S3 W3 mem md k regs (c_sp1 cx + 0x88) (c_p cx + pos1) (c_p cx) (c_n cx) pl HJ).
    - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - rewrite G3. exact Hgp.
    - rewrite G4. exact Htp.
    - rewrite Usp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Qsp1a; [|lia].
      destruct Qsp1a as [q Hq]. exists (2 * q). lia.
    - rewrite Usp. unfold READ_NAME_STK, GB_STK in *. change ASTACK with 16384. lia.
    - rewrite Usp. lia.
    - exact R10.
    - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Qsp1a; [|lia].
      destruct Qsp1a as [q Hq]. exists (4 * q + 17). lia.
    - rewrite Usp. lia.
    - apply (val_mem_of_rdword SEGS (w_H W3) mem). exact C88.
    - rewrite Lpl. apply (val_mem_of_rdword SEGS (w_H W3) mem).
      replace (c_sp1 cx + 136 + 8) with (c_sp1 cx + 144) by lia. exact C90.
    - apply (c3_stk_ra B LAWS ly3 S3 W3 mem md);
        [exact HAR3 | rewrite Eslo; unfold GB_STK in *; lia | lia | rewrite Eshi; lia].
    - intros a Ha. split; [left; unfold GB_STK in *; lia|].
      split; [apply HPRES; unfold GB_STK in *; lia|].
      split; [apply (al_stack _ _ LAWS ly3 S3 W3 mem md a HAR3); rewrite Eslo, Eshi; unfold GB_STK in *; lia|].
      rewrite Usp. lia.
    - lia.
    - rewrite Lpl. lia.
    - rewrite Lpl. destruct Hinp as [(Hn0 & Hp0) | (Hn & Hin)].
      + left. rewrite Hp0. unfold GB_EMPTY. lia.
      + destruct Hinp3 as [Hn0 | (_ & _ & H1 & H2 & Happ)]; [lia|].
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
        apply (amem_range_sub_app (c_p cx) (req_size (c_n cx))); [exact Happ | lia | lia | lia | lia].
    - intros Hne. destruct Hinp3 as [Hn0 | (_ & Hin3 & _)].
      + exfalso. apply Hne. apply length_zero_iff_nil. lia.
      + split; [exact Hin3|]. lia.
    - intros j Hj. rewrite Lpl in Hj. subst pl. rewrite nth_skipn.
      assert (Hjl : (Z.to_nat pos1 + Z.to_nat j < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat)
        by (rewrite length_map; unfold c_n in *; lia).
      destruct (HIN _ Hjl) as (Hv & Hr).
      rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv, Hr by exact Hjl. rewrite map_nth in Hv, Hr.
      replace (c_p cx + pos1 + j) with (c_p cx + Z.of_nat (Z.to_nat pos1 + Z.to_nat j)) by lia.
      apply (aview_of_val_mem1 SEGS (w_H W3) mem); [exact Hv | exact Hr].
    - unfold GB_EV in Hev. unfold EV_READ_NAME. lia.
    - rewrite (blocks_bytes_bsum B ly3 S3), HBLK, c3a_bsum_app.
      rewrite (blocks_bytes_bsum B (c_ly cx) (c_S cx)) in Hlive.
      cbn [bsum fold_right snd]. unfold GB_LIVE, LIVE_READ_NAME, REG_SIZE in *. lia.
    - apply (mok_station MT (c_S cx) S3 (c_T cx) acc _ MTL HMOK HMO); [apply mo_malloc_nonneg; [exact MTL | lia]|].
      pose proof (mo_malloc_mono MT MTL (read_name_c.rn_k pl + 1) 48 ltac:(lia)) as M1.
      pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)) as M2. pose proof (mo_free_nonneg MT MTL) as M3.
      unfold GB_NEED, GB_A in *. nia.
    - exact HRNTR. }
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & s & -> & HJ2 & HP2 & R10' & Hfr2 & Hs4096 & Hab2 & _ & _ & Hname
    & Hc1 & Hc2 & Hmle & Hkept).
  rewrite Usp in Hkept.
  pose proof HJ2 as (HAR2 & _).
  assert (HFR2 : frames S2 = [(GB_CID, fp)]) by (rewrite Hfr2; exact HFR).
  set (kk := read_name_c.rn_k pl) in *.
  assert (Hab2' : ablocks B ly2 S2 = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (s, kk + 1)])
    by (rewrite Hab2, HBLK, <- app_assoc; reflexivity).
  assert (Hsin : In (s, kk + 1) (ablocks B ly2 S2))
    by (rewrite Hab2'; apply in_or_app; right; right; left; reflexivity).
  assert (HrIn2 : In (r, REG_SIZE) (ablocks B ly2 S2))
    by (rewrite Hab2'; apply in_or_app; right; left; reflexivity).
  assert (Hsnot : ~ In (s, kk + 1) (ablocks B (c_ly cx) (c_S cx)))
    by (apply (c3_not_entry B LAWS cx ly2 S2 W2 mem2 md2 s (kk + 1) [(r, REG_SIZE); (s, kk + 1)] HAR2 Hab2');
        right; left; reflexivity).
  assert (HIN3 : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn0; destruct Hinp3 as [Hz | (_ & Hin3 & _)]; [lia | exact Hin3]).
  assert (HIN2 : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly2 S2))
    by (intros Hn0; rewrite Hab2; apply in_or_app; left; exact (HIN3 Hn0)).
  pose proof (req_size_pos (kk + 1) ltac:(lia)) as [_ Hsq].
  assert (Hne : (r, REG_SIZE) <> (s, kk + 1)) by (intros Heq; injection Heq as _ Hq; unfold REG_SIZE in Hq; lia).
  pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 r REG_SIZE s (kk + 1) HAR2 HrIn2 Hsin Hne) as Hdrs.
  unfold zdisjoint in Hdrs. cbn [fst snd] in Hdrs. change (req_size REG_SIZE) with 288 in Hdrs.
  destruct Hkept as (K1 & K2 & _ & K4 & _).
  assert (NE : forall a, c3_at0 cx fp a -> ~ read_name_c.rn_writes (c_sp1 cx + 0x88) s kk a).
  { intros a Ha [Hw | Hw].
    - destruct (c3a_at_cur ly3 S3 W3 mem md k a HJ HFR Ha) as (_ & Hn). apply Hn. lia.
    - apply (c3_newblk_apart B MT LAWS cx fp ly2 S2 W2 mem2 md2 _ s (kk + 1) a HB HJ2 HFR2 Hsin Hsnot HIN2 Ha).
      lia. }
  assert (MK : forall a, c3_at0 cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem a).
  { apply (c3_kept_at B MT LAWS cx fp ly3 S3 W3 W2 mem md k mem2 (c_sp1 cx - READ_NAME_STK)
      (read_name_c.rn_writes (c_sp1 cx + 0x88) s kk) HB HJ HFR HIN3).
    - unfold READ_NAME_STK. change ASTACK with 16384. lia.
    - exact NE.
    - split; [exact K1|]. split; [exact K2 | exact K4]. }
  assert (KP : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs2 q = getr regs q).
  { intros q Hq. pose proof (HP2 (bv_unsigned q) Hq) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
  assert (Htnu : 0 <= tread_name_used pl <= Z.of_nat (length pl)) by (unfold tread_name_used; fold kk; lia).
  pose proof (LLVMFuzzerTestOneInput_rn.rn_name_len pl) as Lnm. fold kk in Lnm.
  pose proof (c3a_nm_len (Boxreg.bsub pl 1 kk)) as Lnm2.
  apply (HK ly2 S2 W2 (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 (k + EV_READ_NAME)
           (acc + mo_malloc MT (kk + 1)) r bs idxb (pos1 + tread_name_used pl) s (kk + 1) op
           (LLVMFuzzerTestOneInput_rn.nm_str (Boxreg.bsub pl 1 kk ++ [Z_to_bv 8 0]))).
  - exact HJ2.
  - exact HFR2.
  - exact (mle_station MT (c_S cx) S3 S2 acc _ MTL HMO Hmle).
  - exact Hi.
  - unfold EV_READ_NAME. lia.
  - pose proof (mo_malloc_mono MT MTL (kk + 1) 48 ltac:(lia)) as M1. unfold GB_A in *. nia.
  - cbn [ms_pc_val mkst]. exact R1.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold gregs. cbn [ms_regs mkst].
    split; [rewrite (KP 2%bv c3_cs2); exact G2|].
    split; [rewrite (KP 8%bv c3_cs8); exact G8|].
    split; [rewrite (KP 9%bv c3_cs9); exact G9|].
    split; [rewrite (KP 3%bv c3_cs3); exact G3|].
    split; [rewrite (KP 4%bv c3_cs4); exact G4|].
    split; [rewrite (KP 18%bv c3_cs18); exact G18 | rewrite (KP 24%bv c3_cs24); exact G24].
  - cbn [ms_regs mkst]. exact R10'.
  - cbn [ms_regs mkst]. rewrite (KP 20%bv c3_cs20). exact R20.
  - cbn [ms_regs mkst]. rewrite (KP 21%bv c3_cs21). exact R21.
  - cbn [ms_regs mkst]. rewrite (KP 22%bv c3_cs22). exact R22.
  - cbn [ms_regs mkst]. rewrite (KP 25%bv c3_cs25). exact R25.
  - cbn [ms_regs mkst]. rewrite (KP 26%bv c3_cs26). exact R26.
  - exact Hidx.
  - exact Hop.
  - cbn [ms_mem mkst]. exact (c3_M_keep cx fp W3 W2 r _ i bs mem mem2 HM MK).
  - split; [lia|]. unfold gslot. cbn [ms_mem mkst]. split.
    + replace (c_p cx + (pos1 + tread_name_used pl)) with (c_p cx + pos1 + tread_name_used pl) by lia.
      apply (rdword_of_val_mem SEGS (w_H W2) mem2); [exact Hc1 | lia].
    + replace (c_n cx - (pos1 + tread_name_used pl)) with (Z.of_nat (length pl) - tread_name_used pl) by lia.
      replace (c_sp1 cx + 144) with (c_sp1 cx + 136 + 8) by lia.
      apply (rdword_of_val_mem SEGS (w_H W2) mem2); [exact Hc2 | lia].
  - split; [exact HrIn2|]. split; [exact Hlen|]. intros j Hj. cbn [ms_mem mkst].
    rewrite (K2 r REG_SIZE j HrIn3) by (change (req_size REG_SIZE) with 288; unfold REG_SIZE in Hj; lia ||
      (unfold read_name_c.rn_writes, REG_SIZE in *; unfold GB_STK in *; lia)).
    exact (HR j Hj).
  - exact Hab2'.
  - lia.
  - exact HIN2.
  - exact Hinv.
  - apply LLVMFuzzerTestOneInput_rn.nm_str_ok.
  - lia.
  - intros j Hj. cbn [ms_mem mkst]. rewrite (Hname j) by lia. f_equal. apply c3a_nm. lia.
Qed.

(* ---- the walk 0x803fc .. 0x80580, split on the bytes left at the cursor ---- *)
Definition c3a_T (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (r : Z) (bs : list byte) (pos op : Z) : Prop :=
  gb_body cx fp (GP_T 3) W3 ms3 GSH_it /\ 0 <= i < 64 /\ k <= 1 + 2 * i /\ acc <= GB_A MT i /\
  gblk1 B cx ly3 S3 r /\ greg B ly3 S3 W3 ms3 r bs /\ gprev cx fp W3 ms3 bs /\ Boxreg.boxreg_inv bs /\
  0 <= op < 256 /\ Z.land op 3 = 3 /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 22 = w64 op /\
  getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs) /\ getr (ms_regs ms3) 26 = w64 (Boxreg.bx_n bs) /\
  gslots_r cx fp W3 ms3 r (Boxreg.bx_fabric bs) /\ gcursor cx W3 ms3 pos /\
  gslot cx W3 ms3 0x68 i /\ (3 <= 1 -> gslot cx W3 ms3 0x48 (Boxreg.bx_n bs)).

Lemma c3a_M_of : forall k acc ly3 S3 W3 ms3 r bs pos op,
  c3a_T k acc ly3 S3 W3 ms3 r bs pos op -> c3_M0 cx fp W3 r (Boxreg.bx_fabric bs) i bs (ms_mem ms3).
Proof.
  intros k acc ly3 S3 W3 ms3 r bs pos op
    (HBODY & _ & _ & _ & _ & _ & HPREV & _ & _ & _ & _ & _ & _ & _ & HSR & _ & S68 & _).
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & HSV & HSH & _ & HFL & HSF & HIN).
  change (fs_frame_bytes GB_CID) with 512 in HFL.
  replace (gF cx fp + 512 - 8) with (gF cx fp + 504) in HFL by lia.
  exact (conj HSV (conj HSH (conj HFL (conj HIN (conj HSF (conj HSR (conj S68 HPREV))))))).
Qed.

(* No byte left (n - pos = 0): `beqz` goes to 0x80578, s5 = 0, and the cursor is as it was. *)
Lemma c3a_n0 : forall k acc ly3 S3 W3 ms3 md3 r bs pos op,
  c3a_K ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  c3a_T k acc ly3 S3 W3 ms3 r bs pos op -> c_n cx - pos = 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros k acc ly3 S3 W3 ms3 md3 r bs pos op HK HJ HFR HMO HI HCASE.
  pose proof (c3a_M_of k acc ly3 S3 W3 ms3 r bs pos op HI) as HM.
  destruct HI as (HBODY & Hi & Hk & Hacc & HBLK & HREG & HPREV & HINV & Hop & Hop3 & R20 & R22 & R25 & R26 & HSR
    & HCUR & S68 & _).
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HGR & _).
  pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24).
  pose proof HCUR as (Hpos & C88 & C90).
  pose proof HREG as (_ & HlBS & HR3).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
  pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
  pose proof (c3_geo B MT LAWS cx fp ly3 S3 W3 (ms_mem ms3) md3 k HB HJ HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold GB_STK in Qsp.
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
  unfold gblk1 in HBLK.
  assert (HrIn3 : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HrIn3) as (_ & Hr4096 & Hrceil & _).
  change (req_size REG_SIZE) with 288 in Hrceil.
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (c_p cx + pos)])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (r0 : bv 5), Z.of_nat q = bv_unsigned r0 -> ew E q = getr (ms_regs ms3) r0)
    by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F32 : ew E 32 = Z_to_bv 64 (c_p cx + pos))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
    by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; unfold GB_STK in *; lia).
  assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF)
    by (rewrite (EE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; vm_compute; split; congruence).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 0x4b0 sr_atoms [C3A_Rsl (SLit 0)] None (C3A_F []))
    (restrict (w_H W3) ms3)).
  { rewrite (c3_mkst ms3 (w_H W3) 0x4b0 Hpc Hresv Hsvc Hrom Hfregs Hfcsr). apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold YP09.region_ok, C3A_Rsl. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold GB_STK in *; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val SEGS E _ _ 0x88 8 (SOff 32 0) (c_p cx + pos));
          [rewrite denot_off0; exact F32 | cbn; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact C88.
      + apply (chunk_ok_val SEGS E _ _ 0x90 8 (SLit 0) 0);
          [rewrite denot_lit_U, U_lit_val by lia; reflexivity | cbn; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). rewrite <- HCASE. exact C90.
    - cbn. repeat split.
    - split; [|split; exact I]. cbn [C3A_F f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U18. unfold SHADOW_OFF. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [exact I | exact Qsp1a | reflexivity | lia]. }
  assert (SHOK : sh_ok SEGS C3BX [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  paj_run_tok (paj_run B LAWS) HS HJ SHOK C3SPAN.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply awr_ok_cons_ro; [cbn; lia|]
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9; lia | cbn; unfold GB_STK in *; lia | cbn; lia |] ]. }
  assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) ->
    aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hn. apply (c3a_keep_outside E _ _ _ (w_H W3) a HF Ha). intros (rr & Hrr & Hb).
    cbn [ss_mem In] in Hrr.
    repeat (destruct Hrr as [<- | Hrr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi C3A_Rsl C3A_Rin base_val] in Hb; rewrite ?U9 in Hb; lia|]).
    destruct Hrr. }
  clear HF HFr HG.
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [Z_to_bv 64 (c_p cx + pos)]) E)
    by (split; [intros q Hq; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (KP : forall r0 : bv 5, In r0 c3a_kl -> getr (ms_regs ms) r0 = getr (ms_regs ms3) r0)
    by (intros r0 Hr; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms) (ms_regs ms3) _ c3a_kl HS HAE
          ltac:(vm_compute; reflexivity) r0 Hr)).
  pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRG. cbn [ms_mem restrict] in HRG.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (21%bv : bv 5) Q21.
  pmkst HS. rewrite pa_sigma_read_name.
  change (SRr SEGS W3 (cfg_at SEGS A_read_nameP (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md3) mat md3)) (POST cx)).
  apply (c3a_call k acc ly3 S3 W3 _ (ms_regs ms) (ms_mem ms) r bs pos op 0 HK HJ HFR HMO Hi Hk Hacc HBLK HlBS).
  - intros j Hj. rewrite M1 by (unfold REG_SIZE in Hj; unfold GB_STK in *; lia). exact (HR3 j Hj).
  - exact HINV.
  - exact Hop.
  - lia.
  - apply (c3_M_keep cx fp W3 W3 r _ i bs (ms_mem ms3) (ms_mem ms) HM).
    intros a Ha. destruct (c3a_at_cur ly3 S3 W3 (ms_mem ms) _ _ a HJ HFR Ha) as (Ha1 & Ha2).
    exact (M1 a Ha1 Ha2).
  - exact Hpos.
  - apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
    rewrite <- U9. exact (field_of_region E _ 9%nat _ _ _ _ _ _ 0x88 8 (SOff 32 0) (c_p cx + pos) HRG eq_refl
      ltac:(cbn; tauto) ltac:(rewrite denot_off0; exact F32) ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite HCASE. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
    rewrite <- U9. exact (field_of_region E _ 9%nat _ _ _ _ _ _ 0x90 8 (SLit 0) 0 HRG eq_refl
      ltac:(cbn; tauto) ltac:(rewrite denot_lit_U, U_lit_val by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite (KP 2%bv) by (cbn; tauto). exact G2.
  - rewrite (KP 8%bv) by (cbn; tauto). exact G8.
  - rewrite (KP 9%bv) by (cbn; tauto). exact G9.
  - rewrite (KP 3%bv) by (cbn; tauto). exact G3.
  - rewrite (KP 4%bv) by (cbn; tauto). exact G4.
  - rewrite (KP 18%bv) by (cbn; tauto). exact G18.
  - rewrite (KP 24%bv) by (cbn; tauto). exact G24.
  - exact Q1.
  - rewrite Q10, U9. reflexivity.
  - rewrite (KP 20%bv) by (cbn; tauto). exact R20.
  - exact Q21.
  - rewrite (KP 22%bv) by (cbn; tauto). exact R22.
  - rewrite (KP 25%bv) by (cbn; tauto). exact R25.
  - rewrite (KP 26%bv) by (cbn; tauto). exact R26.
Qed.

(* At least one byte left: the shadow test of p passes, the cursor advances by one, s5 = the byte at p. *)
Lemma c3a_n1 : forall k acc ly3 S3 W3 ms3 md3 r bs pos op,
  c3a_K ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  c3a_T k acc ly3 S3 W3 ms3 r bs pos op -> 1 <= c_n cx - pos ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros k acc ly3 S3 W3 ms3 md3 r bs pos op HK HJ HFR HMO HI HCASE.
  pose proof (c3a_M_of k acc ly3 S3 W3 ms3 r bs pos op HI) as HM.
  destruct HI as (HBODY & Hi & Hk & Hacc & HBLK & HREG & HPREV & HINV & Hop & Hop3 & R20 & R22 & R25 & R26 & HSR
    & HCUR & S68 & _).
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HGR & _).
  pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24).
  pose proof HCUR as (Hpos & C88 & C90).
  pose proof HREG as (_ & HlBS & HR3).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
  pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
  pose proof (c3_geo B MT LAWS cx fp ly3 S3 W3 (ms_mem ms3) md3 k HB HJ HFR) as
    (Q16 & Qsp & Qsp1 & Qsp1a & QF0 & QFc & QSH & Qp0 & Qpn & Qn).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold GB_STK in Qsp.
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
  unfold gblk1 in HBLK.
  assert (HrIn3 : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HrIn3) as (_ & Hr4096 & Hrceil & _).
  change (req_size REG_SIZE) with 288 in Hrceil.
  assert (Hn1 : In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ 4096 <= c_p cx /\
    c_p cx + req_size (c_n cx) <= alloc_ceiling).
  { pose proof HB as (_ & _ & _ & Hinp & _). destruct Hinp as [(Hn0 & _) | (Hn & Hin)]; [lia|].
    assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (rewrite HBLK; apply in_or_app; left; exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _).
    split; [exact Hin3|]. lia. }
  destruct Hn1 as (Hin3 & Hp4096 & Hpceil).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
  pose proof HM as (_ & _ & _ & HIN & _).
  set (b0 := bv_unsigned (nth (Z.to_nat pos) (c_pl cx) (Z_to_bv 8 0))).
  assert (Hb0 : aview SEGS (w_H W3) (ms_mem ms3) (c_p cx + pos) = Some b0 /\ 0 <= b0 < 256).
  { assert (Hjl : (Z.to_nat pos < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat)
      by (rewrite length_map; unfold c_n in *; lia).
    destruct (HIN _ Hjl) as (Hv & Hr). rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv, Hr by exact Hjl.
    rewrite map_nth in Hv, Hr.
    replace (c_p cx + Z.of_nat (Z.to_nat pos)) with (c_p cx + pos) in Hv by lia.
    split; [apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms3)); [exact Hv | exact Hr] | exact Hr]. }
  destruct Hb0 as (Hb0 & Hb0r).
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (c_p cx + pos); Z_to_bv 64 (c_n cx - pos); Z_to_bv 64 b0])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (r0 : bv 5), Z.of_nat q = bv_unsigned r0 -> ew E q = getr (ms_regs ms3) r0)
    by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F32 : ew E 32 = Z_to_bv 64 (c_p cx + pos))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (F33 : ew E 33 = Z_to_bv 64 (c_n cx - pos))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (F34 : ew E 34 = Z_to_bv 64 b0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
    by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; unfold GB_STK in *; lia).
  assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF)
    by (rewrite (EE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; vm_compute; split; congruence).
  assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (rewrite F32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = c_n cx - pos) by (rewrite F33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = b0) by (rewrite F34; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi SEGS VAL E (mkSS 0x4b0 sr_atoms [C3A_Rsl (SOff 33 0); C3A_Rin] None
    (C3A_F [(32%nat, mkAF 0 (2 ^ 47 - 2) 0); (33%nat, mkAF 1 (2 ^ 26) 0); (34%nat, mkAF 0 255 0)]))
    (restrict (w_H W3) ms3)).
  { rewrite (c3_mkst ms3 (w_H W3) 0x4b0 Hpc Hresv Hsvc Hrom Hfregs Hfcsr). apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold YP09.region_ok, C3A_Rsl. cbv zeta.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
        split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold GB_STK in *; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS E _ _ 0x88 8 (SOff 32 0) (c_p cx + pos));
            [rewrite denot_off0; exact F32 | cbn; lia | cbn; lia |].
          apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact C88.
        * apply (chunk_ok_val SEGS E _ _ 0x90 8 (SOff 33 0) (c_n cx - pos));
            [rewrite denot_off0; exact F33 | cbn; lia | cbn; lia |].
          apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact C90.
      + unfold YP09.region_ok, C3A_Rin. cbv zeta.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 34 0) b0); [rewrite denot_off0; exact F34 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (proj1 (c3a_val_mem1 W3 (ms_mem ms3) _ _ Hb0)).
    - apply pairwise_disjoint_of_extents. unfold C3A_Rsl, C3A_Rin, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat match goal with |- _ /\ _ => split end; first [exact I | unfold GB_STK in *; lia].
    - split; [|split; exact I]. cbn [C3A_F f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U18, U32, U33, U34. unfold SHADOW_OFF. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [exact I | exact Qsp1a | reflexivity | lia]. }
  assert (SHOK : sh_ok SEGS C3BX [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  paj_run_tok (paj_run B LAWS) HS HJ SHOK C3SPAN.
  { unfold C3BX. assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
    rewrite (U_off_val E 18 SHADOW_OFF 0 F18) by (vm_compute; split; congruence).
    rewrite (U_off_val E 32 (c_p cx + pos) 0 F32) by lia. rewrite !Z.add_0_r.
    exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) (c_p cx + pos) 1
      HAR3 Hin3 ltac:(lia) ltac:(lia)). }
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply awr_ok_cons_ro; [cbn; lia|]
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9; lia | cbn; unfold GB_STK in *; lia | cbn; lia |] ]. }
  lazymatch type of HS with st_ok _ ?E2 _ _ => set (E1 := E2) in * end.
  assert (EW : forall n, (n < 512)%nat -> ew E1 n = ew E n)
    by (intros n Hn; subst E1; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) ->
    aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hn. apply (c3a_keep_outside E _ _ _ (w_H W3) a HF Ha). intros (rr & Hrr & Hb).
    cbn [ss_mem In] in Hrr.
    repeat (destruct Hrr as [<- | Hrr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi C3A_Rsl C3A_Rin base_val] in Hb; rewrite ?U9 in Hb; lia|]).
    destruct Hrr. }
  clear HF HFr HG.
  assert (HAE : env_agree 32
    (Ereg (ms_regs ms3) [Z_to_bv 64 (c_p cx + pos); Z_to_bv 64 (c_n cx - pos); Z_to_bv 64 b0]) E1)
    by (split; [intros q Hq; rewrite EW by lia; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (KP : forall r0 : bv 5, In r0 c3a_kl -> getr (ms_regs ms) r0 = getr (ms_regs ms3) r0)
    by (intros r0 Hr; exact (regs_kept_of_st_ok SEGS E1 _ (restrict (w_H W3) ms) (ms_regs ms3) _ c3a_kl HS HAE
          ltac:(vm_compute; reflexivity) r0 Hr)).
  pose proof (st_ok_region_nth E1 _ _ 0 _ HS eq_refl) as HRG. cbn [ms_mem restrict] in HRG.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (21%bv : bv 5) Q21.
  pmkst HS. rewrite pa_sigma_read_name.
  change (SRr SEGS W3 (cfg_at SEGS A_read_nameP (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md3) mat md3)) (POST cx)).
  assert (U9' : bv_unsigned (ew E1 9) = c_sp1 cx) by (rewrite EW by lia; exact U9).
  assert (F32' : ew E1 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite EW by lia; exact F32).
  assert (F33' : ew E1 33 = Z_to_bv 64 (c_n cx - pos)) by (rewrite EW by lia; exact F33).
  apply (c3a_call k acc ly3 S3 W3 _ (ms_regs ms) (ms_mem ms) r bs (pos + 1) op b0 HK HJ HFR HMO Hi Hk Hacc HBLK
           HlBS).
  - intros j Hj. rewrite M1 by (unfold REG_SIZE in Hj; unfold GB_STK in *; lia). exact (HR3 j Hj).
  - exact HINV.
  - exact Hop.
  - exact Hb0r.
  - apply (c3_M_keep cx fp W3 W3 r _ i bs (ms_mem ms3) (ms_mem ms) HM).
    intros a Ha. destruct (c3a_at_cur ly3 S3 W3 (ms_mem ms) _ _ a HJ HFR Ha) as (Ha1 & Ha2).
    exact (M1 a Ha1 Ha2).
  - lia.
  - replace (c_p cx + (pos + 1)) with (c_p cx + pos + 1) by lia.
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
    rewrite <- U9'. exact (field_of_region E1 _ 9%nat _ _ _ _ _ _ 0x88 8 (SOff 32 1) (c_p cx + pos + 1) HRG eq_refl
      ltac:(cbn; tauto) ltac:(apply (denot_off_val E1 32 (c_p cx + pos) 1 F32'); lia) ltac:(cbn; lia) ltac:(cbn; lia)).
  - replace (c_n cx - (pos + 1)) with (c_n cx - pos + -1) by lia.
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
    rewrite <- U9'. exact (field_of_region E1 _ 9%nat _ _ _ _ _ _ 0x90 8 (SOff 33 (-1)) (c_n cx - pos + -1) HRG
      eq_refl ltac:(cbn; tauto) ltac:(apply (denot_off_val E1 33 (c_n cx - pos) (-1) F33'); lia)
      ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite (KP 2%bv) by (cbn; tauto). exact G2.
  - rewrite (KP 8%bv) by (cbn; tauto). exact G8.
  - rewrite (KP 9%bv) by (cbn; tauto). exact G9.
  - rewrite (KP 3%bv) by (cbn; tauto). exact G3.
  - rewrite (KP 4%bv) by (cbn; tauto). exact G4.
  - rewrite (KP 18%bv) by (cbn; tauto). exact G18.
  - rewrite (KP 24%bv) by (cbn; tauto). exact G24.
  - exact Q1.
  - rewrite Q10, U9'. reflexivity.
  - rewrite (KP 20%bv) by (cbn; tauto). exact R20.
  - rewrite Q21, EW by lia. exact F34.
  - rewrite (KP 22%bv) by (cbn; tauto). exact R22.
  - rewrite (KP 25%bv) by (cbn; tauto). exact R25.
  - rewrite (KP 26%bv) by (cbn; tauto). exact R26.
Qed.

End e.
End d.

(* ---- the segment: BoxLxCase3Top.v's C3SEGA ---- *)
Theorem c3_segA : forall (cx : bcx) (fp : Z) (POST : bcx -> world SEGS -> config -> Prop) (i : Z),
  gb_base B MT cx ->
  (forall ly' S' W' (ms' : machine_state) md' k' acc' r bs idxb pos nm szn op sstr,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(GB_CID, fp)] ly' S' W' (ms_mem ms') md' k' ->
  frames S' = [(GB_CID, fp)] -> mo_le MT (c_S cx) S' acc' ->
  0 <= i < 64 -> k' <= 2 + 2 * i -> acc' + mo_free MT <= GB_A MT (i + 1) ->
  ms_pc_val ms' = w64 (BASE + 0x638) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx fp ms' ->
  getr (ms_regs ms') 10 = w64 nm -> getr (ms_regs ms') 20 = w64 r ->
  getr (ms_regs ms') 21 = Z_to_bv 64 idxb -> getr (ms_regs ms') 22 = w64 op ->
  getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) -> getr (ms_regs ms') 26 = w64 (Boxreg.bx_n bs) ->
  0 <= idxb < 256 -> 0 <= op < 256 ->
  c3_M0 cx fp W' r (Boxreg.bx_fabric bs) i bs (ms_mem ms') ->
  gcursor cx W' ms' pos ->
  greg B ly' S' W' ms' r bs ->
  ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE); (nm, szn)] ->
  0 < szn <= 48 ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S')) ->
  Boxreg.boxreg_inv bs ->
  Forall (fun c => 0 < c < 256) sstr -> Z.of_nat (length sstr) + 1 <= szn ->
  (forall j, 0 <= j <= Z.of_nat (length sstr) ->
  aview SEGS (w_H W') (ms_mem ms') (nm + j) = Some (nth (Z.to_nat j) (sstr ++ [0]) 0)) ->
  SRr SEGS W' (mkCfg ms' md') (POST cx)) ->
  forall k acc ly3 S3 W3 (ms3 : machine_state) md3,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  GI_T B MT 3 i cx fp k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros cx fp POST i HB HK k acc ly3 S3 W3 ms3 md3 HJ HFR HMO HI.
  destruct HI as (r & bs & pos & op & HI).
  assert (HT : c3a_T cx fp i k acc ly3 S3 W3 ms3 r bs pos op) by exact HI.
  pose proof HT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hpos & _) & _).
  destruct (Z.eq_dec (c_n cx - pos) 0) as [H0 | H0].
  - exact (c3a_n0 cx fp POST i HB k acc ly3 S3 W3 ms3 md3 r bs pos op HK HJ HFR HMO HT H0).
  - exact (c3a_n1 cx fp POST i HB k acc ly3 S3 W3 ms3 md3 r bs pos op HK HJ HFR HMO HT ltac:(lia)).
Qed.
End c.
End b.
End a.
