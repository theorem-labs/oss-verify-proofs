(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlDecode YajlFactsBits YajlFactsLex YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib RY_decode1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BI_globals2 BI_lowshadow BYajlRep BYajl_iface BYajlAlign BY_ubkit BY_rz BY_hand BY_client BY_dec1 BY_dec2 BY_dec3 BY_dec4 BY_dec5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lkr := rewrite ?app_nil_r; repeat match goal with H : ?l = [] |- context [?l] => rewrite H end; cbn [app]; rewrite ?app_nil_r.
Ltac lk0 := lkr; reflexivity.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma nbig_app2 : forall l1 l2, nbig (l1 ++ l2) = nbig l1 + nbig l2.
Proof. aceil. intros. unfold nbig. rewrite filter_app, length_app. lia. Qed.
Lemma nbig_le_len2 : forall l, nbig l <= Z.of_nat (length l).
Proof. aceil. intros l. unfold nbig. induction l as [|b l IH]; cbn; [lia|]. destruct (64512 <? ab_size b); cbn; lia. Qed.
Lemma ff_bytes_0 : ff_bytes 0 = 64. Proof. reflexivity. Qed.
Lemma dForall_firstn : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (firstn k l).
Proof. aceil. intros A P k l H. revert k. induction H; intros [|k]; cbn; constructor; auto. Qed.
Lemma dForall_skipn : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. aceil. intros A P k l H. revert k. induction H; intros [|k]; cbn; try constructor; auto. Qed.
Lemma dForall_zslice : forall (P : Z -> Prop) str i k, Forall P str -> Forall P (zslice str i k).
Proof. aceil. intros. unfold zslice. apply dForall_firstn, dForall_skipn. assumption. Qed.
Lemma shl8_0 : Z.shiftl 8 0 = 8. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition litc (k : Z) : Z := nth (Z.to_nat k) [63; 13; 10; 92; 47; 34; 12; 8; 9] 0.
Definition LIT0 : Z := 0x21e40.

Lemma lit_cases : forall k, 0 <= k < 9 -> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8.
Proof. aceil. intros; lia. Qed.

(* [comment removed for export] *)
Lemma lit_bytes : forall m k, mem_inv bsegs m -> 0 <= k < 9 ->
  bytes_at bsegs m (LIT0 + 32 * k) (zbytes ([litc k] ++ 0 :: [0; 0; 0; 0; 0; 0])).
Proof. aceil.
  intros m k MI Hk. unfold LIT0.
  destruct (lit_cases k Hk) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; cbn;
  lazymatch goal with |- bytes_at _ _ ?A ?bs =>
    let R := fresh in
    pose proof (ro_cells_image bsegs m A bs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as R;
    apply ro_cells_bytes_at in R; cbn [cells_bytes cbytes app] in R; exact R end.
Qed.

(* [comment removed for export] *)
Lemma lit_window : forall m k n, low_shadow_ok m -> 0 <= k < 9 -> 1 <= n <= 2 ->
  exists ws, shadow_window bsegs m 2147450880 (LIT0 + 32 * k) n ws /\ range_clean 2147450880 (LIT0 + 32 * k) n ws
         /\ 0x7fffc3c8 <= shw_lo 2147450880 (LIT0 + 32 * k) /\ shw_hi 2147450880 (LIT0 + 32 * k) n <= 0x7fffc3f0.
Proof. aceil.
  intros m k n LS Hk Hn. unfold LIT0.
  pose proof (shw_geom 2147450880 (138816 + 32 * k) n ltac:(lia) ltac:(lia) ltac:(lia)) as G; cbv zeta in G.
  set (lo := shw_lo 2147450880 (138816 + 32 * k)) in *. set (hi := shw_hi 2147450880 (138816 + 32 * k) n) in *.
  assert (E1 : Z.shiftr (138816 + 32 * k) 3 = 17352 + 4 * k) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (E2 : Z.shiftr (138816 + 32 * k + n + -1) 3 = 17352 + 4 * k) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  rewrite E1, E2 in G.
  assert (HLO : LS_LO <= lo) by lia. assert (HHI : hi <= LS_HI) by lia.
  exists (low_shadow_bytes lo (Z.to_nat (hi - lo))). split; [| split; [| lia]].
  - split; [apply low_shadow_bytes_at; [exact LS| lia| lia]| rewrite low_shadow_bytes_length; lia].
  - intros g Hg. rewrite E1, E2 in Hg. assert (g = 17352 + 4 * k) as -> by lia.
    exists (Z_to_bv 8 2). split; [| right; split; [symmetry; exact E2|]].
    + rewrite low_shadow_bytes_nth by lia. f_equal. replace (lo + Z.of_nat (Z.to_nat (2147450880 + (17352 + 4 * k) - lo))) with (2147468232 + 4 * k) by lia.
      destruct (lit_cases k Hk) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute; reflexivity.
    + change (bv_signed (Z_to_bv 8 2)) with 2. clear -CEILB Hk Hn. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma u5_window : forall m FF n b0 b1 b2 b3 b5 b6 b7, FF mod 64 = 0 -> 0 <= FF -> 1 <= n <= 5 ->
  rw_cells bsegs m (FF / 8 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 (Z_to_bv 8 5); C1 b5; C1 b6; C1 b7] ->
  shadow_window bsegs m 2147450880 (FF + 32) n [b0; b1; b2; b3; Z_to_bv 8 5; b5; b6; b7] /\ range_clean 2147450880 (FF + 32) n [b0; b1; b2; b3; Z_to_bv 8 5; b5; b6; b7]
  /\ shw_lo 2147450880 (FF + 32) = FF / 8 + 2147450880 /\ shw_hi 2147450880 (FF + 32) n = FF / 8 + 2147450880 + 8.
Proof. aceil.
  intros m FF n b0 b1 b2 b3 b5 b6 b7 A64 F0 Hn SH.
  assert (E1 : shw_lo 2147450880 (FF + 32) = FF / 8 + 2147450880).
  { unfold shw_lo, al8. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear SH. Z.div_mod_to_equations. lia. }
  assert (E2 : shw_hi 2147450880 (FF + 32) n = FF / 8 + 2147450880 + 8).
  { unfold shw_hi, al8. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear SH. Z.div_mod_to_equations. lia. }
  split; [| split; [| auto]].
  - split; [| rewrite E1, E2; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia]. rewrite E1.
    destruct SH as [[_ SB] _]. cbn [cells_bytes cbytes app] in SB. exact SB.
  - intros g Hg. rewrite !Z.shiftr_div_pow2 in Hg by lia. change (2^3) with 8 in Hg.
    assert (GR : g = FF / 8 + 4) by (clear SH E1 E2; Z.div_mod_to_equations; lia).
    exists (Z_to_bv 8 5). split.
    + rewrite E1. replace (Z.to_nat (2147450880 + g - (FF / 8 + 2147450880))) with 4%nat by lia. reflexivity.
    + right. split; [rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear SH E1 E2; Z.div_mod_to_equations; lia|].
      change (bv_signed (Z_to_bv 8 5)) with 5. clear SH E1 E2. Z.div_mod_to_equations. lia.
Qed.

Lemma u8enc_facts : forall cp, 0 < cp < 2097152 ->
  Forall (fun c => 0 < c < 256) (RY_decode1.u8enc cp) /\ (1 <= length (RY_decode1.u8enc cp) <= 4)%nat.
Proof. aceil.
  intros cp H.
  destruct (Z_lt_le_dec cp 128) as [L1|G1].
  { rewrite (RY_decode1.u8enc_1 cp) by lia. split; [constructor; [lia| constructor]| cbn; lia]. }
  destruct (Z_lt_le_dec cp 2048) as [L2|G2].
  { destruct (RY_decode1.u8enc_2 cp ltac:(lia)) as (-> & R0 & R1). split; [repeat constructor; lia| cbn; lia]. }
  destruct (Z_lt_le_dec cp 65536) as [L3|G3].
  { destruct (RY_decode1.u8enc_3 cp ltac:(lia)) as (-> & R0 & R1 & R2). split; [repeat constructor; lia| cbn; lia]. }
  destruct (RY_decode1.u8enc_4 cp ltac:(lia)) as (-> & R0 & R1 & R2 & R3). split; [repeat constructor; lia| cbn; lia].
Qed.

Lemma length_u8out : forall cp ubs, length ubs = 5%nat -> (1 <= length (RY_decode1.u8enc cp) <= 4)%nat -> length (u8out cp ubs) = 5%nat.
Proof. aceil. intros cp ubs L K. unfold u8out. rewrite length_app, zbytes_length. cbn [length]. rewrite length_skipn. lia. Qed.

Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis AFLSEP : AHK_y_aflsep_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis RREFL : ayR_refl_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis STATY : AHK_y_statics_stmt Y.
Hypothesis ASM0 : astack_malloc_stmt Y 0 AY_STACK_MALLOC_0.
Hypothesis FREL : AHK_y_fake_release_stmt Y.
Hypothesis FND : AHK_y_fnodup_stmt Y.
Hypothesis AFLC : AHK_y_flag_cell_stmt Y.
Hypothesis BAPP2 : aybuf_append_stmt Y.
Hypothesis HEX : ayhexToDigit_stmt.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells bsegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
Hypothesis URA_a1 : In 0x8b7e0 URA.      (* [comment removed for export] *)
Hypothesis URA_a2 : In 0x8ba0c URA.      (* [comment removed for export] *)
Hypothesis URA_a3 : In 0x8b9c4 URA.      (* [comment removed for export] *)
Hypothesis URA_a4 : In 0x8bb88 URA.      (* [comment removed for export] *)
Hypothesis ICPG : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals bsegs m A_SB.
Hypothesis ICPG2 : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals2 bsegs m.
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window bsegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).
Hypothesis LOWSH : forall s LB LF m mo, y_AHK Y s LB LF m mo -> low_shadow_ok m.
(* [comment removed for export] *)
Hypothesis SSH0 : forall s LB LF m mo A n, y_AHK Y s LB LF m mo -> alloc_ceiling <= A -> 1 <= n -> A + n <= 2^47 ->
    exists ws, shadow_window bsegs m A_SB A n ws /\ range_clean A_SB A n ws /\ pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n)
               /\ ws = repeat (Z_to_bv 8 0) (length ws).

Ltac rchain := first [eassumption | eapply RRT; [eassumption| rchain]].

(* [comment removed for export] *)
Section Fn.
Variables (LF : list fblock) (REST : list ablock) (mbd : mbuf) (db : ybuf) (AF S : Z) (str : list Z) (n OT OTn lo RR : Z) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (mo : Model) (s : y_APS Y).
Variables (SQ FF : Z).
Let B := mb_addr mbd.
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : y_APS Y) (db' : ybuf) (mbd' : mbuf) (LK : list ablock),
     aystring_decode_rpost Y sp m mo s LF REST mbd db AF S str n OT OTn lo RR a0' fc' m' mo' s' db' mbd' LK ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis TP : tp = Z_to_bv 64 (c_tp ACONSTS).
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AY_DECODE_STACK.
Hypothesis SPH : bv_unsigned sp < 2^47.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis SQR : bv_unsigned sp - 240 <= SQ <= bv_unsigned sp - 224.   (* [comment removed for export] *)
Hypothesis SQ32 : SQ mod 32 = 0.
Hypothesis FFsh : 6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF).   (* [comment removed for export] *)
Hypothesis FFce : FF + 64 <= alloc_ceiling.
Hypothesis FFal : FF mod 64 = 0.
Hypothesis PFR : (6303744 <= y_aflag Y 0 FF /\ (y_aflag Y 0 FF + 1 <= 2147446784 \/ 17594333495296 <= y_aflag Y 0 FF)) /\ y_aflag Y 0 FF + 1 <= alloc_ceiling.   (* [comment removed for export] *)
Hypothesis PFD : y_aflag Y 0 FF + 1 <= FF \/ FF + 64 <= y_aflag Y 0 FF.
Hypothesis FRESH : forall g, In g LF -> In g ((0, FF) :: LF) /\ snd g <> snd (0, FF).
Hypothesis AFIN : exists b, In b REST /\ ab_addr b <= AF /\ AF + 32 <= ab_addr b + 8 * (ab_size b / 8) /\ AF mod 8 = 0 /\ oshw_hi 0 (2^47) <= ab_addr b.   (* [comment removed for export] *)
Hypothesis SF : Forall (fun c => 0 <= c < 256) str.
Hypothesis NL : n = zlength str.
Hypothesis N26 : n < 2^26.
Hypothesis SNZ : S <> 0.
Hypothesis S47 : S + n < 2^47.
Hypothesis TR : (exists bt, In bt REST /\ ab_addr bt <= S /\ S + n <= ab_addr bt + ab_size bt) \/ n = 0.
Hypothesis NBIG : nbig REST <= AY_NBIG_REST + 2.
Hypothesis UA : y_uanchor Y m (bv_unsigned sp) ra s0.
Hypothesis BAD : 0 < B /\ B mod 8 = 0 /\ 0 < AF /\ AF mod 8 = 0.   (* [comment removed for export] *)

Let CEIL' : alloc_ceiling <= lo. Proof. exact CEIL. Qed.
Let LO' : lo <= bv_unsigned sp - (272 + (128 + 8192)). Proof. exact LO. Qed.

(* [comment removed for export] *)
Ltac ba_app EB POS := unfold BA_aybuf_append; rewrite ?EB; pose proof BAD as (BA1' & BA2' & BA3' & BA4');
  split; [exact BA1'|]; split; [exact BA2'|]; split; [exact BA3'|]; split; [exact BA4'| POS].

(* [comment removed for export] *)
Lemma txt_ceiling : forall sx LB LFx mx mox, y_AHK Y sx LB LFx mx mox -> (forall b, In b REST -> In b LB) -> 0 < n -> 0 <= S /\ S + n <= alloc_ceiling.
Proof. aceil.
  intros sx LB LFx mx mox AHK HI NP. destruct TR as [(bt & HBT & T1 & T2)|N0]; [| lia].
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & _ & _). pose proof (RNG bt (HI _ HBT)) as RT.
  unfold ablock_range, ACONSTS in RT. cbn [c_img_hi] in RT. lia.
Qed.

Lemma txt_pres : forall RESTx LFx SPx ma mb, ay_pres RESTx LFx SPx [] ma mb -> (forall b, In b REST -> In b RESTx) ->
  bytes_at bsegs ma S (zbytes str) -> bytes_at bsegs mb S (zbytes str).
Proof. aceil.
  intros RESTx LFx SPx ma mb HP HI TB. destruct TR as [(bt & HBT & T1 & T2)|N0].
  - eapply aypres_block_bytes; [exact HP| exact TB|]. exists bt. split; [exact (HI _ HBT)|]. rewrite zbytes_length. unfold zlength in NL. lia.
  - assert (str = []) as -> by (destruct str; [reflexivity| unfold zlength in *; cbn in *; lia]).
    destruct TB as (B0 & B1 & _). split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
Qed.

Lemma txt_munch : forall W ma mb, munch W ma mb -> Forall (fun iv : Z * Z => snd iv <= 0 \/ alloc_ceiling <= fst iv) W ->
  (0 < n -> 0 <= S /\ S + n <= alloc_ceiling) -> bytes_at bsegs ma S (zbytes str) -> bytes_at bsegs mb S (zbytes str).
Proof. aceil.
  intros W ma mb MU HW STXT TB. destruct str as [|c str'] eqn:ES.
  - destruct TB as (B0 & B1 & _). split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
  - eapply (bytes_at_transport bsegs); [exact TB| exact MU|]. rewrite zbytes_length.
    assert (NP : 0 < n) by (rewrite NL; unfold zlength; cbn; lia). specialize (STXT NP). rewrite NL in STXT. unfold zlength in STXT.
    eapply dForall_disjoint_from; [exact HW| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma yaf_ok_now : forall sx LB LFx mx mox RESTx, y_AHK Y sx LB LFx mx mox ->
  (forall b, In b REST -> In b LB) -> (forall b, In b REST -> In b RESTx) -> ayaf_ok RESTx mx AF.
Proof. aceil.
  intros sx LB LFx mx mox RESTx AHK HI HI2. destruct AFIN as (b & Hb & H1 & H2 & H8 & HHI).
  assert (SZ : 0 < ab_size b) by (clear -CEILB H1 H2; Z.div_mod_to_equations; lia).
  destruct (BSHY _ _ _ _ _ b AHK (HI _ Hb) SZ) as [OS _].
  exists b. split; [exact (HI2 _ Hb)|]. split; [exact H1|]. split; [exact H2|]. split; [exact H8|]. split; [exact OS| exact HHI].
Qed.

(* [comment removed for export] *)
Definition dsaved : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition own_iv (iv : Z * Z) : Prop :=
  fst iv < snd iv /\ ((alloc_ceiling <= fst iv /\ snd iv <= bv_unsigned sp) \/ (FF <= fst iv /\ snd iv <= FF + 64)
                      \/ (FF / 8 + 2147450880 <= fst iv /\ snd iv <= FF / 8 + 2147450880 + 8)).
Lemma own_writes : forall sx LBX mx my moy W,
  y_AHK Y sx LBX ((0, FF) :: LF) mx moy -> munch W mx my -> wmono bsegs mx my -> Forall own_iv W ->
  y_AHK Y sx LBX ((0, FF) :: LF) my moy /\ ay_pres LBX LF (bv_unsigned sp) [] mx my /\ (aystatics mx -> aystatics my).
Proof. aceil.
  intros sx LBX mx my moy W AHK MU WM HW.
  pose proof CEIL' as CE. pose proof FFce as FC. aceil.
  split; [| split].
  - eapply FRAMEY; [exact AHK| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. intros [lo' hi'] [NE [[A1 A2]|[[A1 A2]|[A1 A2]]]]; cbn [fst snd] in *.
    + left. cbn. exact A1.
    + right; right; left. exists (0, FF). split; [left; reflexivity|]. cbn [fst snd]. rewrite ff_bytes_0. lia.
    + right; right; right; left. exists (0, FF). split; [left; reflexivity|]. cbn [fst snd]. unfold oshw_lo, A_SB. rewrite shl8_0. lia.
  - eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _. clear MU WM. induction HW as [| [lo' hi'] W [NE HX] HW IH]; [exact I|].
    cbn [fst snd] in NE, HX. apply outside_cons; [| exact IH].
    destruct HX as [[A1 A2]|[[A1 A2]|[A1 A2]]].
    + eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ _ (bv_unsigned sp)); [exact AHK| intros b0 Hb0; exact Hb0| exact A1| exact A2| exact (ay_client_addr_mono _ _ ((0, FF) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)].
    + eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ _ LF (bv_unsigned sp) (0, FF)); [exact AHK| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| left; cbn [fst snd]; rewrite ff_bytes_0; lia| lia| aceil; lia| exact Hc].
    + eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ _ LF (bv_unsigned sp) (0, FF)); [exact AHK| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| right; cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia| lia| aceil; lia| exact Hc].
  - intros YS. eapply aystatics_munch; [exact YS| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. intros [lo' hi'] [NE [[A1 A2]|[[A1 A2]|[A1 A2]]]]; cbn [fst snd] in *; right; aceil; lia.
Qed.

(* [comment removed for export] *)
Lemma buf_keep : forall sx LBX LK mx my moy mb b,
  y_AHK Y sx (abl (buf_blocks mb b) ++ LK ++ REST) LBX my moy -> ay_pres (abl (buf_blocks mb b) ++ LK ++ REST) LF (bv_unsigned sp) [] mx my ->
  buf_rep bsegs mx mb b AF -> (yb_data b <> None -> oshadow mx (mb_data mb) (yb_len b) /\ amem (mb_data mb) (yb_len b)) ->
  buf_rep bsegs my mb b AF /\ oshadow my (mb_addr mb) SIZEOF_BUF /\ (yb_data b <> None -> oshadow my (mb_data mb) (yb_len b) /\ amem (mb_data mb) (yb_len b)).
Proof. aceil.
  intros sx LBX LK mx my moy mb b AHK PRES BR OSD. split; [| split].
  - eapply (buf_rep_agree bsegs); [eapply ay_pres_agree; exact PRES| exact BR| |].
    + intros a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_addr mb) SIZEOF_BUF). split; [unfold buf_blocks; left; reflexivity| cbn; lia].
    + intros Hd a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_data mb) (yb_len b)).
      split; [unfold buf_blocks; destruct (yb_data b); [right; left; reflexivity| exfalso; apply Hd; reflexivity]| cbn; lia].
  - destruct (BSHY _ _ _ _ _ (mkABlock (mb_addr mb) SIZEOF_BUF) AHK ltac:(unfold buf_blocks; left; reflexivity) ltac:(cbn; unfold SIZEOF_BUF; lia)) as [X _]. exact X.
  - intros Hd. destruct (OSD Hd) as [OD HI]. split; [| exact HI]. destruct (Z.lt_ge_cases 0 (yb_len b)) as [POS|Z0].
    + destruct (BSHY _ _ _ _ _ (mkABlock (mb_data mb) (yb_len b)) AHK ltac:(unfold buf_blocks; destruct (yb_data b); [right; left; reflexivity| exfalso; apply Hd; reflexivity]) POS) as [X _]. exact X.
    + destruct OD as (D8 & Dn & DU). split; [exact D8|]. split; [exact Dn|].
      eapply u8arr_agree; [eapply ay_pres_agree; exact PRES| exact DU|]. rewrite (blk_shadow_length (yb_len b)) by lia.
      intros a Ha. exfalso. clear -CEILB Ha Z0 D8 Dn. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma sshadow_byte : forall sx LBx LFx mx mox A, y_AHK Y sx LBx LFx mx mox -> alloc_ceiling <= A -> A + 8 <= 2^47 -> A mod 8 = 0 ->
  bytes_at bsegs mx (A_SB + A / 8) [Z_to_bv 8 0]
  /\ exists lo' hi', pages_budgeted (y_aS Y sx) lo' hi' /\ lo' <= A_SB + A / 8 /\ A_SB + A / 8 + 1 <= hi' /\ 0 <= lo' /\ hi' < 2^64.
Proof. aceil.
  intros sx LBx LFx mx mox A AHK HA HB A8. pose proof CEIL' as CE.
  destruct (SSH0 _ _ _ _ _ A 1 AHK HA ltac:(lia) ltac:(lia)) as (ws & [WB WL] & _ & PB & WZ).
  pose proof (shw_geom A_SB A 1 ltac:(unfold A_SB; lia) ltac:(aceil; lia) ltac:(lia)) as G; cbv zeta in G.
  rewrite Z.shiftr_div_pow2 in G by lia. change (2^3) with 8 in G.
  split.
  - destruct WB as (B0 & B1 & BB). split; [unfold A_SB; lia|]. split; [cbn [length]; unfold A_SB in *; lia|].
    intros i Hi. cbn [length] in Hi. assert (i = 0%nat) as -> by lia. cbn [nth_error].
    specialize (BB (Z.to_nat (A_SB + A / 8 - shw_lo A_SB A)) ltac:(lia)).
    replace (shw_lo A_SB A + Z.of_nat (Z.to_nat (A_SB + A / 8 - shw_lo A_SB A))) with (A_SB + A / 8) in BB by lia.
    rewrite WZ, nth_error_repeat in BB by lia. rewrite Z.add_0_r. exact BB.
  - exists (shw_lo A_SB A), (shw_hi A_SB A 1). split; [exact PB|]. unfold A_SB in *. lia.
Qed.

(* [comment removed for export] *)
Lemma txt_obj : forall sx LB LFx mx mox, y_AHK Y sx LB LFx mx mox -> (forall b, In b REST -> In b LB) -> 0 < n ->
  exists bt, In bt LB /\ oshadow mx (ab_addr bt) (ab_size bt) /\ ab_addr bt <= S /\ S + n <= ab_addr bt + ab_size bt
             /\ amem (ab_addr bt) (ab_size bt) /\ ab_addr bt + ab_size bt <= alloc_ceiling /\ 0 <= ab_addr bt /\ ab_addr bt mod 8 = 0.
Proof. aceil.
  intros sx LB LFx mx mox AHK HI NP. destruct TR as [(bt & HBT & T1 & T2)|N0]; [| lia].
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & _ & _). pose proof (RNG bt (HI _ HBT)) as RT. unfold ablock_range, ACONSTS in RT. cbn [c_img_hi] in RT.
  destruct (BSHY _ _ _ _ _ bt AHK (HI _ HBT) ltac:(lia)) as [OS OH].
  exists bt. split; [exact (HI _ HBT)|]. split; [exact OS|]. split; [lia|]. split; [lia|]. split; [exact OH|]. split; [lia|]. split; [lia|].
  clear -CEILB RT. destruct RT as (_ & M16 & _). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_exit : forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s6v s7v t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (b : ybuf) (mb : mbuf) (LK : list ablock) (beg' e' : Z)
    (qcs : list cell) (w0f : word) (h0 h1 h2 h3 h4 h5 h6 h7 : byte),
  y_AHK Y s1' (abl (buf_blocks mb b) ++ LK ++ REST) ((0, FF) :: LF) m1 mo1 -> aystatics m1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 120) (bv_unsigned sp + -104) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ qcs -> cells_size qcs = 120%nat ->
  rw_cells bsegs m1 (SQ + 80) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) dsaved ->
  rw_cells bsegs m1 FF [C8 w0f] -> rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 (y_aflag Y 0 FF))] ->
  rw_cells bsegs m1 (FF / 8 + 2147450880) [C1 h0; C1 h1; C1 h2; C1 h3; C1 h4; C1 h5; C1 h6; C1 h7] ->
  bytes_at bsegs m1 S (zbytes str) ->
  rw_cells bsegs m1 AF (alloc_cells ayc) -> buf_rep bsegs m1 mb b AF -> buf_inv b -> mb_same mbd mb ->
  oshadow m1 (mb_addr mb) SIZEOF_BUF -> (yb_data b <> None -> oshadow m1 (mb_data mb) (yb_len b) /\ amem (mb_data mb) (yb_len b)) ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s -> y_phi_buf Y b + RR <= y_acredit Y s1' -> 0 <= RR ->
  (LK <> [] -> yb_state b <> BS_ok /\ length LK = 1%nat) -> LK = [] ->
  yb_used b <= beg' -> 0 <= beg' <= e' -> e' <= n ->
  (forall bf, yleaf (ybuf_append b (zslice str beg' (e' - beg'))) bf -> yleaf (ystring_decode db str n) bf) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                              s2v (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) s6v s7v (Z_to_bv 64 e') (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 beg') t3 t4 t5 t6)
                          F1 (Z_to_bv 64 ADP_EXIT) fc1 None m1 (seg_rom bsegs)) mo1) K.
Proof. aceil.
  intros until h7. intros AHK1 YS1 MI1 ST1 GAP1 FRM1 FRQ FRQsz L112 SV1 FF0 FFP FSH TXT1 YAF1 BR1 BI MBS OSB1 OSD1 PRES1 R1 SO1 CRED1 RR0 LKc ELK UB HBE HEN HL.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof CEIL' as CE. pose proof LO' as LOx. pose proof (zlength_nonneg str) as NL0.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  assert (E8F : FF = 8 * (FF / 8)) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  assert (EB : mb_addr mb = B) by (unfold B; exact MBS).
  assert (INR : forall b0, In b0 REST -> In b0 (abl (buf_blocks mb b) ++ LK ++ REST)) by (intros b0 Hb0; apply in_or_app; right; apply in_or_app; right; exact Hb0).
  (* [comment removed for export] *)
  arz_seg KIPY AHK1.
  eapply evtA_cut.
  { eapply seg_exit; [exact MI1| exact HBE| exact HEN| exact N26| pose proof (proj1 TXT1); lia| exact S47]. }
  cbv beta. intros ms2 (xq & -> & _).
  apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHK2 R2]. clear LINK BACK.
  (* [comment removed for export] *)
  assert (SRCL : zlength (zslice str beg' (e' - beg')) = e' - beg') by (apply zslice_length; lia).
  pose proof (sub_chunk m1 _ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV1)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV16 by lia.
  unfold AY_BUF_APPEND.
  eapply (BAPP2 ((0, FF) :: LF) (LK ++ REST) mb b AF (S + beg') (zslice str beg' (e' - beg')) lo RR K);
    [ ba_app EB ltac:(pose proof (proj1 TXT1); lia)
    | exact K0
    | apply AYST_split; split; [exact AHK2| exact YS1]
    | exact BR1 | exact BI | exact YAF1
    | eapply yaf_ok_now; [exact AHK2| exact INR| intros b0 Hb0; apply in_or_app; right; exact Hb0]
    | exact OSB1
    | intros Hd; exact (proj1 (OSD1 Hd))
    | apply abytes_at_zslice; [exact TXT1| lia]
    | apply dForall_zslice; exact SF
    | intros _; pose proof (proj1 TXT1); lia
    | rewrite SRCL; lia
    | rewrite SRCL; lia
    | (* [comment removed for export] *) unfold ysrc_range; rewrite SRCL;
      destruct (Z.lt_ge_cases 0 (e' - beg')) as [Hn|Hn]; [| right; right; right; clear -CEILB Hn HBE; lia];
      destruct TR as [(bt & HBT & T1 & T2)|N0']; [| exfalso; lia];
      left; exists bt; split; [apply in_or_app; right; exact HBT| lia]
    | (* [comment removed for export] *)
      unfold ysrc_win; rewrite SRCL, USQ; intros Hn s' LBx m' mo' AHK' PRES';
      destruct TR as [(bt & HBT & T1 & T2)|N0']; [| exfalso; lia];
      assert (INx : In bt (LBx ++ LK ++ REST)) by (apply in_or_app; right; apply in_or_app; right; exact HBT);
      destruct (ICPB _ _ _ _ _ bt (S + beg') (e' - beg') AHK' INx ltac:(lia) ltac:(lia) ltac:(lia)) as (ws & SW & RC & SH1' & SH2');
      exists ws; split; [exact SW|]; split; [exact RC|];
      eapply aypol_pages;
      [ eapply ICPR; [exact AHK'| exact INx| lia| lia| lia]
      | pose proof (shw_geom A_SB (S + beg') (e' - beg') ltac:(unfold A_SB; lia) ltac:(pose proof (proj1 TXT1); lia) ltac:(lia)) as G; cbv zeta in G; unfold A_SB in *; clear -CEILB G; lia
      | clear -CEILB SH1'; unfold A_SB in *; lia ]
    | unfold ayframe_pre, AY_BUF_APPEND_STACK, AMALLOC_STACK; aceil; rewrite USQ;
      split; [exact ST1|]; split; [lia|]; split; [unfold AY_DECODE_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK in LO; lia|]; split; [lia|];
      split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|]; split; [exact MI1|]; split; [exact TP| exact FRM1]
    | rewrite EB; reflexivity | reflexivity | rewrite SRCL; reflexivity
    | exact CRED1 | exact RR0
    | rewrite nbig_app2; pose proof (nbig_le_len2 LK); destruct LK; [cbn in *; lia| destruct (LKc ltac:(discriminate)) as [_ L1]; cbn [length] in *; lia]
    | rewrite USQ; eapply USTEP; [unfold ADP_RET5; rewrite unsigned_lit by lia; exact URA_a4| lia| exact SV16
      | eapply UFRAME; [| exact UA]; intros a Ha; destruct (PRES1 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]; exact E]
    | ].
  cbv beta. intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c F3 fc3 m3 mo3 s3' b' mb' LK0 POST.
  destruct POST as (SO3 & R3 & CRED3 & (MI3 & ST3 & FRM3 & _ & PRES3) & YAF3 & YLA & BR3 & MBS3 & OS3 & OSD3 & LKZ3 & AY3 & LKB3 & NLK).
  rewrite USQ in ST3, PRES3.
  replace (ret_pc (Z_to_bv 64 ADP_RET5)) with (Z_to_bv 64 ADP_RET5) by (symmetry; apply ret_pc_even; [unfold ADP_RET5; lia| reflexivity]).
  apply AYST_split in AY3. destruct AY3 as [AHK3 YS3].
  (* [comment removed for export] *)
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 SV1 ltac:(lia)) as SV3. clear SV1 SV16.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 FRQ ltac:(lia)) as FRQ3. clear FRQ.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 L112 ltac:(lia)) as L112_3. clear L112.
  assert (GAP3 : stk bsegs m3 (SQ + 120) (bv_unsigned sp + -104)).
  { eapply stk_agree; [eapply ay_pres_agree; exact PRES3| exact GAP1| intros a Ha; split; [left; lia| intros F0; exact F0]]. }
  clear GAP1.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (0, FF) PRES3 FF0 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_0; lia)) as FF0_3. clear FF0.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (0, FF) PRES3 FFP (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_0; lia)) as FFP3. clear FFP.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (0, FF) PRES3 FSH (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) as FSH3. clear FSH.
  pose proof (txt_pres _ _ _ _ _ PRES3 ltac:(intros b0 Hb0; apply in_or_app; right; exact Hb0) TXT1) as TXT3.
  assert (PRES3w : ay_pres REST LF (bv_unsigned sp) [] m m3).
  { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES3| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0| intros f Hf; right; exact Hf| auto]. }
  clear PRES1 MI1 ST1 TXT1 YAF1 BR1 OSB1 OSD1 AHK1 AHK2 YS1.
  assert (INR3 : forall b0, In b0 REST -> In b0 (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST)).
  { intros b0 Hb0. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hb0. }
  (* [comment removed for export] *)
  destruct (AFLC _ _ _ _ _ (0, FF) AHK3 (or_introl eq_refl)) as [[fl FLG] _]. cbn [fst snd] in FLG.
  (* [comment removed for export] *)
  arz_seg KIPY AHK3.
  pose proof (aypol_fframe Y _ ((0, FF) :: LF) _ _ LINK (0, FF) FF (FF + 64) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; rewrite ff_bytes_0; lia) ltac:(lia) ltac:(cbn; rewrite ff_bytes_0; lia)) as PFF.
  pose proof (aypol_ffshadow Y _ ((0, FF) :: LF) _ _ LINK (0, FF) (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) as PFFS.
  pose proof (aypol_stack Y _ ((0, FF) :: LF) _ _ LINK (SQ + 80) (SQ + 96) ltac:(aceil; lia) ltac:(lia)) as PSQ.
  pose proof (aypol_stack Y _ ((0, FF) :: LF) _ _ LINK (bv_unsigned sp - 256) (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  assert (PPF : acc_ok (m_vm_lazy mo3) (y_aS Y s3') (Z_to_bv 64 (y_aflag Y 0 FF), 1%nat)).
  { apply LINK. unfold ay_acc. cbn [fst snd]. rewrite unsigned_lit by lia. do 6 right. left. exists (0, FF). split; [left; reflexivity|]. cbn [fst snd]. split; [reflexivity| reflexivity]. }
  eapply evtA_cut.
  { eapply adp_epi1; [ exact MI3 | lia | lia | exact L112_3 | exact FF0_3 | exact FFP3 | exact FSH3 | lia | aceil; lia | exact FFal
                     | aceil; lia | exact PSQ | exact PFF | exact PFFS ]. }
  cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & FSH4 & FF0_4 & FFP4 & L112_4).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FLG MU4 WM4 ltac:(cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; aceil; lia)) as FLG4.
  pose proof (rw_cells_transport bsegs _ _ _ _ _ SV3 MU4 WM4 ltac:(cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; aceil; lia)) as SV4.
  eapply evtA_cut.
  { eapply adp_epi2; [ exact MI4 | exact FLG4 | exact SV4 | lia | aceil; lia | lia | lia | exact PPF | exact PSTK ]. }
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & FL5 & SV5).
  apply evtA_done. intros mo5 Hag5 HLI5 Hh5. destruct (BACK mo5 Hag5 HLI5) as [AHKb R5]. clear LINK BACK PFF PFFS PSQ PSTK PPF.
  (* [comment removed for export] *)
  assert (AHK4 : y_AHK Y s3' (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST) ((0, FF) :: LF) m4 mo5).
  { eapply FRAMEY; [exact AHKb| exact MU4| exact WM4|].
    constructor; [right; right; right; left; exists (0, FF); split; [left; reflexivity| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia]|].
    constructor; [right; right; left; exists (0, FF); split; [left; reflexivity| cbn [fst snd]; rewrite ff_bytes_0; lia]| constructor]. }
  pose proof (FREL _ _ _ _ _ _ 0 FF AHK4 (or_introl eq_refl) MU5 WM5 FL5) as AHK5.
  cbn [ff_remove fst snd] in AHK5. rewrite !Z.eqb_refl in AHK5. cbn [andb] in AHK5.
  pose proof (aystatics_munch _ _ _ YS3 MU4 WM4 ltac:(constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; aceil; lia| constructor]])) as YS4.
  pose proof (aystatics_munch _ _ _ YS4 MU5 WM5 ltac:(constructor; [cbn [fst snd]; aceil; lia| constructor])) as YS5.
  (* [comment removed for export] *)
  assert (PRES45 : ay_pres (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST) LF (bv_unsigned sp) [] m3 m5).
  { eapply ay_pres_trans.
    - eapply ay_pres_of_munch; [exact MU4| exact WM4|]. intros a Ha Hc _.
      apply outside_cons; [| apply outside_cons; [| exact I]].
      + eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ _ LF (bv_unsigned sp) (0, FF)); [exact AHK3| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| right; cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia| lia| aceil; lia| exact Hc].
      + eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ _ LF (bv_unsigned sp) (0, FF)); [exact AHK3| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| left; cbn [fst snd]; rewrite ff_bytes_0; lia| lia| aceil; lia| exact Hc].
    - eapply ay_pres_of_munch; [exact MU5| exact WM5|]. intros a Ha Hc _.
      eapply (ay_client_outside_flag Y LAYY AFLSEP _ _ _ _ _ _ LF (bv_unsigned sp) (0, FF)); [exact AHK4| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| aceil; lia| exact Hc]. }
  assert (PRES5 : ay_pres REST LF (bv_unsigned sp) [] m m5).
  { eapply ay_pres_trans; [exact PRES3w|]. eapply (ay_pres_weaken Y); [exact PRES45| lia| exact INR3| intros f Hf; exact Hf| auto]. }
  (* [comment removed for export] *)
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FRQ3 MU4 WM4 ltac:(cbv [disjoint_from fst snd]; rewrite FRQsz; aceil; lia)) as FRQ4.
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FRQ4 MU5 WM5 ltac:(cbv [disjoint_from fst snd]; rewrite FRQsz; aceil; lia)) as FRQ5.
  pose proof (stk_transport_disjoint bsegs _ _ _ _ _ ST3 MU4 WM4 ltac:(cbv [disjoint_from fst snd]; aceil; lia)) as ST4.
  pose proof (stk_transport_disjoint bsegs _ _ _ _ _ ST4 MU5 WM5 ltac:(cbv [disjoint_from fst snd]; aceil; lia)) as ST5.
  pose proof (stk_transport_disjoint bsegs _ _ _ _ _ GAP3 MU4 WM4 ltac:(cbv [disjoint_from fst snd]; aceil; lia)) as GAP4.
  pose proof (stk_transport_disjoint bsegs _ _ _ _ _ GAP4 MU5 WM5 ltac:(cbv [disjoint_from fst snd]; aceil; lia)) as GAP5.
  pose proof (stk_release bsegs _ _ _ _ ST5 FRQ5 ltac:(lia)) as ST6. rewrite FRQsz in ST6. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in ST6.
  pose proof (stk_merge bsegs _ _ _ _ ST6 GAP5 ltac:(lia)) as ST7.
  pose proof (stk_release bsegs _ _ _ _ ST7 SV5 ltac:(lia)) as ST8. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ST8.
  replace (bv_unsigned sp + -104 + 104) with (bv_unsigned sp) in ST8 by lia.
  (* [comment removed for export] *)
  pose proof (aypres_block _ _ _ _ _ _ _ PRES45 YAF3 ltac:(destruct AFIN as (ba & Hba & A1 & A2 & _); exists ba; split; [apply INR3; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB A1 A2; Z.div_mod_to_equations; lia)) as YAF5.
  pose proof (txt_pres _ _ _ _ _ PRES45 INR3 TXT3) as TXT5.
  assert (BUFP : forall a, (mb_addr mb' <= a < mb_addr mb' + SIZEOF_BUF \/ (yb_data b' <> None /\ mb_data mb' <= a < mb_data mb' + yb_len b')) ->
                 ay_client_addr (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST) LF (bv_unsigned sp) a /\ ~ yin_ivs [] a).
  { intros a Ha. split; [| intros F0; exact F0]. right; left.
    unfold buf_blocks. destruct Ha as [Ha|[Hd Ha]].
    - exists (mkABlock (mb_addr mb') SIZEOF_BUF). split; [left; reflexivity| cbn; lia].
    - destruct (yb_data b'); [| exfalso; apply Hd; reflexivity].
      exists (mkABlock (mb_data mb') (yb_len b')). split; [right; left; reflexivity| cbn; lia]. }
  assert (BR5 : buf_rep bsegs m5 mb' b' AF).
  { eapply buf_rep_agree; [eapply ay_pres_agree; exact PRES45| exact BR3| intros a Ha; apply BUFP; left; exact Ha| intros Hd a Ha; apply BUFP; right; split; [exact Hd| exact Ha]]. }
  assert (OS5 : oshadow m5 (mb_addr mb') SIZEOF_BUF).
  { destruct (BSHY _ _ _ _ _ (mkABlock (mb_addr mb') SIZEOF_BUF) AHK5 ltac:(unfold buf_blocks; left; reflexivity) ltac:(cbn; unfold SIZEOF_BUF; lia)) as [X _]. exact X. }
  assert (OSD5 : yb_data b' <> None -> oshadow m5 (mb_data mb') (yb_len b') /\ amem (mb_data mb') (yb_len b')).
  { intros Hd. destruct (OSD3 Hd) as [OD HI]. split; [| exact HI]. destruct (Z.lt_ge_cases 0 (yb_len b')) as [POS|Z0].
    - destruct (BSHY _ _ _ _ _ (mkABlock (mb_data mb') (yb_len b')) AHK5 ltac:(unfold buf_blocks; destruct (yb_data b'); [right; left; reflexivity| exfalso; apply Hd; reflexivity]) POS) as [X _]. exact X.
    - destruct OD as (D8 & Dn & DU). split; [exact D8|]. split; [exact Dn|].
      eapply u8arr_agree; [eapply ay_pres_agree; exact PRES45| exact DU|]. rewrite (blk_shadow_length (yb_len b')) by lia.
      intros a Ha. exfalso. clear -CEILB Ha Z0 D8 Dn. Z.div_mod_to_equations. lia. }
  pose proof (ypost_yleaf _ _ _ (ybuf_append_post2 b (zslice str beg' (e' - beg')) BI ltac:(rewrite SRCL; lia)) YLA) as AP. cbv beta in AP.
  destruct AP as (BI' & APok & APerr).
  eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m5 mo5 s3' b' mb' (LK0 ++ LK)). unfold aystring_decode_rpost.
  split; [rewrite SO3; exact SO1|].
  split; [eapply RRT; [exact R1|]; eapply RRT; [exact R2|]; eapply RRT; [exact R3| exact R5]|].
  split; [exact CRED3|].
  split; [split; [exact MI5|]; split; [exact ST8|]; split; [exact FRM3|]; split; [exact I| exact PRES5]|].
  split; [exact YAF5|].
  split; [apply HL; exact YLA|].
  split; [exact BR5|].
  split; [unfold mb_same in *; congruence|].
  split; [exact OS5|]. split; [exact OSD5|]. split; [exact TXT5|].
  split; [lk0|].
  split.
  - apply AYST_split. split; [| exact YS5]. rewrite <- app_assoc. exact AHK5.
  - intros NE. destruct LK0 as [|k0 LK0'].
    + cbn [app] in *. destruct (LKc NE) as [SB L1]. split; [| exact L1]. intros OK'. apply SB. exact (proj1 (APok OK')).
    + destruct (LKB3 ltac:(discriminate)) as [SB' L1]. specialize (NLK ltac:(discriminate)).
      destruct LK as [|k LK']; [rewrite app_nil_r; split; [exact SB'| exact L1]|].
      exfalso. destruct (LKc ltac:(discriminate)) as [SB _]. exact (SB NLK).
Qed.

Let WHOLE := ydecode_loop (decode_fuel n) db str n 0 0.

Lemma exit_leaf : forall b' beg' e', yleaf WHOLE (b', beg', e') ->
  forall bf, yleaf (ybuf_append b' (zslice str beg' (e' - beg'))) bf -> yleaf (ystring_decode db str n) bf.
Proof. aceil. intros b' beg' e' HW bf HA. unfold ystring_decode. eapply yleaf_bind; [exact HW|]. cbv beta iota. exact HA. Qed.

(* [comment removed for export] *)
Definition head_ok (f : nat) : Prop :=
  forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (b : ybuf) (mb : mbuf) (LK : list ablock) (beg e : Z)
    (w0 w96 sur cp : word) (ubs : list byte) (wf0 wf8 wf16 : word) (j24 j37 : list byte),
  y_AHK Y s1' (abl (buf_blocks mb b) ++ LK ++ REST) ((0, FF) :: LF) m1 mo1 -> aystatics m1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 120) (bv_unsigned sp + -104) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ (dspill w0 w96 FF sur cp) ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) dsaved ->
  rw_cells bsegs m1 FF [C8 wf0; C8 wf8; C8 wf16; CB 8 j24] -> rw_cells bsegs m1 (FF + 32) [CB 5 ubs] -> rw_cells bsegs m1 (FF + 37) [CB 19 j37] ->
  rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 (y_aflag Y 0 FF))] ->
  rw_cells bsegs m1 (FF / 8 + 2147450880) fsh_out ->
  bytes_at bsegs m1 S (zbytes str) ->
  rw_cells bsegs m1 AF (alloc_cells ayc) -> buf_rep bsegs m1 mb b AF -> buf_inv b -> mb_same mbd mb ->
  oshadow m1 (mb_addr mb) SIZEOF_BUF -> (yb_data b <> None -> oshadow m1 (mb_data mb) (yb_len b) /\ amem (mb_data mb) (yb_len b)) ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s -> y_phi_buf Y b + RR <= y_acredit Y s1' -> 0 <= RR ->
  (LK <> [] -> yb_state b <> BS_ok /\ length LK = 1%nat) -> LK = [] ->
  yb_used b <= beg -> 0 <= beg <= e -> e < n -> sbody_ix str e n -> (Z.to_nat (n - e) < f)%nat ->
  (forall r, yleaf (ydecode_loop f b str n beg e) r -> yleaf WHOLE r) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) s7v (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 beg) t3 t4 t5 t6)
                          F1 (Z_to_bv 64 ADP_HEAD) fc1 None m1 (seg_rom bsegs)) mo1) K.

(* [comment removed for export] *)
Lemma dec_tail : forall f', head_ok f' ->
  forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (b1 : ybuf) (mb1 : mbuf) (LK : list ablock) (p e2 U : Z) (us slk : list Z)
    (w0 w96 sur cp : word) (ubs : list byte) (wf0 wf8 wf16 : word) (j24 j37 : list byte),
  y_AHK Y s1' (abl (buf_blocks mb1 b1) ++ LK ++ REST) ((0, FF) :: LF) m1 mo1 -> aystatics m1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 120) (bv_unsigned sp + -104) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ (dspill w0 w96 FF sur cp) ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) dsaved ->
  rw_cells bsegs m1 FF [C8 wf0; C8 wf8; C8 wf16; CB 8 j24] -> rw_cells bsegs m1 (FF + 32) [CB 5 ubs] -> rw_cells bsegs m1 (FF + 37) [CB 19 j37] ->
  rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 (y_aflag Y 0 FF))] ->
  rw_cells bsegs m1 (FF / 8 + 2147450880) fsh_in ->
  bytes_at bsegs m1 S (zbytes str) ->
  rw_cells bsegs m1 AF (alloc_cells ayc) -> buf_rep bsegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 ->
  oshadow m1 (mb_addr mb1) SIZEOF_BUF -> (yb_data b1 <> None -> oshadow m1 (mb_data mb1) (yb_len b1) /\ amem (mb_data mb1) (yb_len b1)) ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s -> y_phi_buf Y b1 + RR <= y_acredit Y s1' -> 0 <= RR ->
  (LK <> [] -> yb_state b1 <> BS_ok /\ length LK = 1%nat) -> LK = [] ->
  (* [comment removed for export] *)
  bytes_at bsegs m1 U (zbytes (us ++ 0 :: slk)) -> Forall (fun c => 0 <= c < 256) (us ++ 0 :: slk) -> ~ In 0 us -> (1 <= length us <= 4)%nat ->
  (- (U + zlength us + 1)) mod 8 <= zlength slk -> zlength slk <= 7 ->
  ((exists k, 0 <= k < 9 /\ U = LIT0 + 32 * k /\ length us = 1%nat) \/ U = FF + 32) ->
  yb_used b1 + zlength us <= p + 1 -> 0 <= p -> p + 1 <= n -> sbody_ix str (p + 1) n -> (Z.to_nat (n - p) <= f')%nat -> 0 <= e2 < 2^32 ->
  (forall r, yleaf (b2 <- ybuf_append b1 us ;; ydecode_loop f' b2 str n (p + 1) (p + 1)) r -> yleaf WHOLE r) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 U) (Z_to_bv 64 e2) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 p) t3 t4 t5 t6)
                          F1 (Z_to_bv 64 ADP_TAIL) fc1 None m1 (seg_rom bsegs)) mo1) K.
Proof. aceil.
  intros f' HEAD. intros until j37.
  intros AHK1 YS1 MI1 ST1 GAP1 FRM1 FRQ SV1 FFA U5 FJ FFP FSH TXT1 YAF1 BR1 BI MBS OSB1 OSD1 PRES1 R1 SO1 CRED1 RR0 LKc ELK UB UF UN UL USL SLK UK HUSED P0 PN SBP HF E2R HL.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof CEIL' as CE. pose proof LO' as LOx. pose proof (zlength_nonneg str) as NL0.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  assert (E8F : FF = 8 * (FF / 8)) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  assert (EB : mb_addr mb1 = B) by (unfold B; exact MBS).
  assert (INR : forall b0, In b0 REST -> In b0 (abl (buf_blocks mb1 b1) ++ LK ++ REST)) by (intros b0 Hb0; apply in_or_app; right; apply in_or_app; right; exact Hb0).
  pose proof (bytes_at_bound _ _ _ _ UB) as UBB. rewrite zbytes_length, length_app in UBB. cbn [length] in UBB.
  assert (ZLU : 1 <= zlength us <= 4) by (unfold zlength; lia). assert (ZLS : zlength slk = Z.of_nat (length slk)) by reflexivity.
  assert (UU : 0 < U /\ U + zlength us + 1 + zlength slk <= alloc_ceiling /\ U + 5 < 2^47).
  { aceil. destruct UK as [(k & Hk & -> & L1)| ->]; unfold LIT0; lia. }
  rewrite zbytes_app in UB. cbn [zbytes map app] in UB. change (map (Z_to_bv 8) slk) with (zbytes slk) in UB.
  (* [comment removed for export] *)
  arz_seg KIPY AHK1.
  assert (SWX : exists ws, shadow_window bsegs m1 2147450880 U (Z.of_nat (length (zbytes us)) + 1) ws /\ range_clean 2147450880 U (Z.of_nat (length (zbytes us)) + 1) ws
                 /\ pol (acc_ok (m_vm_lazy mo1) (y_aS Y s1')) (shw_lo 2147450880 U) (shw_hi 2147450880 U (Z.of_nat (length (zbytes us)) + 1))).
  { rewrite zbytes_length. destruct UK as [(k & Hk & EU & L1)| EU].
    - rewrite L1. change (Z.of_nat 1 + 1) with 2. destruct (lit_window m1 k 2 (LOWSH _ _ _ _ _ AHK1) Hk ltac:(lia)) as (ws & SW & RC & WL & WH). rewrite <- EU in SW, RC, WL, WH.
      exists ws. split; [exact SW|]. split; [exact RC|].
      eapply (aypol_imgshadow Y _ _ _ _ LINK); unfold oshw_lo, oshw_hi, AY_IMG_LO, AY_IMG_HI, A_SB;
        [replace (2147450880 + 65536 / 8) with 2147459072 by reflexivity| replace (2147450880 + 65536 / 8 + (6303744 - 65536 + 7) / 8) with 2148238848 by reflexivity]; lia.
    - subst U. unfold fsh_in, F1b, F3b in FSH. destruct (u5_window m1 FF (Z.of_nat (length us) + 1) _ _ _ _ _ _ _ FFal ltac:(lia) ltac:(lia) FSH) as (SW & RC & WL & WH).
      eexists. split; [exact SW|]. split; [exact RC|]. rewrite WL, WH.
      eapply (aypol_ffshadow Y _ ((0, FF) :: LF) _ _ LINK (0, FF)); [left; reflexivity| cbn [snd]; unfold oshw_lo, A_SB; lia| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia| lia| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia]. }
  destruct SWX as (ws & SW & RC & PSH).
  assert (PSTR : pol (acc_ok (m_vm_lazy mo1) (y_aS Y s1')) U (U + (Z.of_nat (length (zbytes us)) + 1) + Z.of_nat (length (zbytes slk)))).
  { rewrite !zbytes_length. destruct UK as [(k & Hk & EU & L1)| EU].
    - intros a kk Ha Hk'. eapply (aypol_img Y _ _ _ _ LINK); unfold AY_IMG_LO, AY_IMG_HI, LIT0 in *; lia.
    - subst U. eapply (aypol_fframe Y _ ((0, FF) :: LF) _ _ LINK (0, FF)); [left; reflexivity| cbn; lia| cbn; rewrite ff_bytes_0; unfold zlength in SLK; lia| lia| cbn; rewrite ff_bytes_0; aceil; lia]. }
  pose proof (aypol_img Y _ _ _ _ LINK) as PIMG. pose proof (aypol_stack Y _ ((0, FF) :: LF) _ _ LINK lo SQ CEIL ltac:(lia)) as PSTK.
  eapply evtA_cut.
  { eapply (seg_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SQ B S n U lo (zbytes us) (zbytes slk) ws);
      [ exact MI1 | exact ST1 | exact CEIL | lia | lia
      | rewrite zbytes_length; lia
      | apply zbytes_no_nul; [exact (proj1 (proj1 (Forall_app _ _ _) UF))| exact UN]
      | rewrite !zbytes_length; unfold zlength in USL; exact USL
      | lia
      | rewrite !zbytes_length; unfold zlength in UU; lia
      | exact UB
      | exact (ICPG _ _ _ _ _ AHK1) | exact (ICPG2 _ _ _ _ _ AHK1)
      | exact SW | exact RC | exact PSH | exact PSTR
      | unfold AY_IMG_LO, AY_IMG_HI in PIMG; exact PIMG | exact PSTK ]. }
  cbv beta. intros ms2 (q0 & q1 & q2 & x3 & x4 & x5 & x6 & x7 & q3 & q4 & q5 & q6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & UB2 & _ & _).
  apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHKb R2]. clear LINK BACK PSH PSTR PIMG PSTK.
  (* [comment removed for export] *)
  assert (AHK2 : y_AHK Y s1' (abl (buf_blocks mb1 b1) ++ LK ++ REST) ((0, FF) :: LF) m2 mo2).
  { eapply FRAMEY; [exact AHKb| exact MU2| exact WM2|]. constructor; [left; cbn [fst]; lia| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS1 MU2 WM2 ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS2.
  assert (PRES12 : ay_pres (abl (buf_blocks mb1 b1) ++ LK ++ REST) LF (bv_unsigned sp) [] m1 m2).
  { eapply ay_pres_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc _. apply outside_cons; [| exact I].
    eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ _ (bv_unsigned sp)); [exact AHK1| intros b0 Hb0; exact Hb0| aceil; lia| lia| exact (ay_client_addr_mono _ _ ((0, FF) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)]. }
  Ltac tr12 H MU2 WM2 := eapply (rw_cells_transport bsegs) in H; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; first [lia| aceil; lia]].
  unfold dspill in FRQ. unfold dsaved in SV1. unfold fsh_in in FSH.
  tr12 FRQ MU2 WM2. tr12 SV1 MU2 WM2. tr12 FFA MU2 WM2. tr12 U5 MU2 WM2. tr12 FJ MU2 WM2. tr12 FFP MU2 WM2. tr12 FSH MU2 WM2.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES12 YAF1 ltac:(destruct AFIN as (ba & Hba & A1 & A2 & _); exists ba; split; [apply INR; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB A1 A2; Z.div_mod_to_equations; lia)) as YAF2. clear YAF1. rename YAF2 into YAF1.
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
  pose proof (txt_munch _ _ _ MU2 ltac:(constructor; [cbn [fst snd]; right; lia| constructor]) ltac:(intros NP; exact (txt_ceiling _ _ _ _ _ AHK1 INR NP)) TXT1) as TXT2.
  assert (BR2 : buf_rep bsegs m2 mb1 b1 AF).
  { eapply (buf_rep_agree bsegs); [eapply ay_pres_agree; exact PRES12| exact BR1| |].
    - intros a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_addr mb1) SIZEOF_BUF). split; [unfold buf_blocks; left; reflexivity| cbn; lia].
    - intros Hd a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_data mb1) (yb_len b1)).
      split; [unfold buf_blocks; destruct (yb_data b1); [right; left; reflexivity| exfalso; apply Hd; reflexivity]| cbn; lia]. }
  assert (OSB2 : oshadow m2 (mb_addr mb1) SIZEOF_BUF).
  { destruct (BSHY _ _ _ _ _ (mkABlock (mb_addr mb1) SIZEOF_BUF) AHK2 ltac:(unfold buf_blocks; left; reflexivity) ltac:(cbn; unfold SIZEOF_BUF; lia)) as [X _]. exact X. }
  assert (OSD2 : yb_data b1 <> None -> oshadow m2 (mb_data mb1) (yb_len b1) /\ amem (mb_data mb1) (yb_len b1)).
  { intros Hd. destruct (OSD1 Hd) as [OD HI]. split; [| exact HI]. destruct (Z.lt_ge_cases 0 (yb_len b1)) as [POS|Z0].
    - destruct (BSHY _ _ _ _ _ (mkABlock (mb_data mb1) (yb_len b1)) AHK2 ltac:(unfold buf_blocks; destruct (yb_data b1); [right; left; reflexivity| exfalso; apply Hd; reflexivity]) POS) as [X _]. exact X.
    - destruct OD as (D8 & Dn & DU). split; [exact D8|]. split; [exact Dn|].
      eapply (u8arr_transport bsegs); [exact DU| exact MU2| exact WM2|]. rewrite (blk_shadow_length (yb_len b1)) by lia.
      cbv [disjoint_from fst snd]. unfold A_SB in *; aceil. clear -CEILB Z0 D8 Dn CE SQR LOx. Z.div_mod_to_equations. lia. }
  clear MI1 ST1 TXT1 BR1 OSB1 OSD1 AHK1 YS1.
  (* [comment removed for export] *)
  pose proof (sub_chunk m2 _ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV1)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV16 by lia.
  destruct (proj1 (Forall_app _ us (0 :: slk)) UF) as [UF1 UF2].
  pose proof (proj1 (proj1 (bytes_at_app _ _ _ _ _) UB2)) as UB1.
  unfold AY_BUF_APPEND. rewrite zbytes_length. change (Z.of_nat (length us)) with (zlength us).
  eapply (BAPP2 ((0, FF) :: LF) (LK ++ REST) mb1 b1 AF U us lo RR K);
    [ ba_app EB ltac:(lia)
    | exact K0
    | apply AYST_split; split; [exact AHK2| exact YS2]
    | exact BR2 | exact BI | exact YAF1
    | eapply yaf_ok_now; [exact AHK2| exact INR| intros b0 Hb0; apply in_or_app; right; exact Hb0]
    | exact OSB2
    | intros Hd; exact (proj1 (OSD2 Hd))
    | exact UB1
    | exact UF1
    | intros _; lia
    | lia
    | lia
    | (* [comment removed for export] *) unfold ysrc_range; destruct UK as [(k & Hk & EU & L1)| EU];
        [ right; left; unfold LIT0 in EU; lia
        | right; right; left; exists (0, FF); split; [left; reflexivity| cbn [fst snd]; rewrite ff_bytes_0; lia] ]
    | (* [comment removed for export] *) unfold ysrc_win; rewrite USQ; intros Hn s' LBx m' mo' AHK' PRES';
      destruct (KIPY _ _ _ _ _ AHK') as (_ & _ & _ & LINK' & _);
      destruct UK as [(k & Hk & EU & L1)| EU];
      [ replace (zlength us) with 1 by (unfold zlength; rewrite L1; reflexivity);
        destruct (lit_window m' k 1 (LOWSH _ _ _ _ _ AHK') Hk ltac:(lia)) as (ws' & SW' & RC' & WL' & WH'); rewrite <- EU in SW', RC', WL', WH';
        exists ws'; split; [exact SW'|]; split; [exact RC'|];
        eapply (aypol_imgshadow Y _ _ _ _ LINK'); unfold oshw_lo, oshw_hi, AY_IMG_LO, AY_IMG_HI, A_SB;
        [replace (2147450880 + 65536 / 8) with 2147459072 by reflexivity| replace (2147450880 + 65536 / 8 + (6303744 - 65536 + 7) / 8) with 2148238848 by reflexivity]; lia
      | subst U;
        pose proof (aypres_fframe _ _ _ _ _ _ _ (0, FF) PRES' FSH (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) as FSH';
        unfold fsh_in, F1b, F3b in FSH'; destruct (u5_window m' FF (zlength us) _ _ _ _ _ _ _ FFal ltac:(lia) ltac:(lia) FSH') as (SW' & RC' & WL' & WH');
        eexists; split; [exact SW'|]; split; [exact RC'|]; rewrite WL', WH';
        eapply (aypol_ffshadow Y _ ((0, FF) :: LF) _ _ LINK' (0, FF)); [left; reflexivity| cbn [snd]; unfold oshw_lo, A_SB; lia| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia| lia| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia] ]
    | unfold ayframe_pre, AY_BUF_APPEND_STACK, AMALLOC_STACK; aceil; rewrite USQ;
      split; [exact ST2|]; split; [lia|]; split; [unfold AY_DECODE_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK in LO; lia|]; split; [lia|];
      split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|]; split; [exact MI2|]; split; [exact TP| exact FRM1]
    | rewrite EB; reflexivity | reflexivity | reflexivity
    | exact CRED1 | exact RR0
    | rewrite nbig_app2; pose proof (nbig_le_len2 LK); destruct LK; [cbn in *; lia| destruct (LKc ltac:(discriminate)) as [_ L1]; cbn [length] in *; lia]
    | rewrite USQ; eapply USTEP; [unfold ADP_RET4'; rewrite unsigned_lit by lia; exact URA_a3| lia| exact SV16
      | eapply UFRAME; [| exact UA]; intros a Ha;
        destruct (PRES1 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E1 _];
        destruct (PRES12 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E2 _]; rewrite E2; exact E1]
    | ].
  fold fsh_in in FSH.
  cbv beta. intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c F3 fc3 m3 mo3 s3' b' mb' LK0 POST.
  destruct POST as (SO3 & R3 & CRED3 & (MI3 & ST3 & FRM3 & _ & PRES3) & YAF3 & YLA & BR3 & MBS3 & OS3 & OSD3 & LKZ3 & AY3 & LKB3 & NLK).
  rewrite USQ in ST3, PRES3.
  replace (ret_pc (Z_to_bv 64 ADP_RET4')) with (Z_to_bv 64 ADP_RET4') by (symmetry; apply ret_pc_even; [unfold ADP_RET4'; lia| reflexivity]).
  apply AYST_split in AY3. destruct AY3 as [AHK3 YS3].
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 SV1 ltac:(lia)) as SV3. clear SV1 SV16.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 FRQ ltac:(lia)) as FRQ3. clear FRQ.
  assert (GAP3 : stk bsegs m3 (SQ + 120) (bv_unsigned sp + -104)).
  { eapply stk_agree; [eapply ay_pres_agree; exact PRES3| exact GAP1| intros a Ha; split; [left; lia| intros F0; exact F0]]. }
  clear GAP1.
  Ltac trff H PRES3 FF := first
    [ pose proof (aypres_fframe _ _ _ _ _ _ _ (0, FF) PRES3 H (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_0; lia))
    | pose proof (aypres_fframe _ _ _ _ _ _ _ (0, FF) PRES3 H (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) ].
  trff FFA PRES3 FF. trff U5 PRES3 FF. trff FJ PRES3 FF. trff FFP PRES3 FF. unfold fsh_in in FSH. trff FSH PRES3 FF.
  clear FFA U5 FJ FFP FSH. rename H into FFA3. rename H0 into U53. rename H1 into FJ3. rename H2 into FFP3. rename H3 into FSH3.
  pose proof (txt_pres _ _ _ _ _ PRES3 ltac:(intros b0 Hb0; apply in_or_app; right; exact Hb0) TXT2) as TXT3.
  assert (PRES3w : ay_pres REST LF (bv_unsigned sp) [] m m3).
  { eapply ay_pres_trans; [exact PRES1|]. eapply ay_pres_trans.
    - eapply (ay_pres_weaken Y); [exact PRES12| lia| exact INR| intros f Hf; exact Hf| auto].
    - eapply (ay_pres_weaken Y); [exact PRES3| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0| intros f Hf; right; exact Hf| auto]. }
  assert (INR3 : forall b0, In b0 REST -> In b0 (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST)).
  { intros b0 Hb0. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hb0. }
  pose proof (ypost_yleaf _ _ _ (ybuf_append_post2 b1 us BI ltac:(lia)) YLA) as AP. cbv beta in AP. destruct AP as (BI' & APok & APerr).
  assert (UB' : yb_used b' <= p + 1).
  { destruct (yb_state b') eqn:EST; [destruct (APok eq_refl) as (_ & -> & _); lia| destruct (APerr ltac:(discriminate)) as [-> _]; lia| destruct (APerr ltac:(discriminate)) as [-> _]; lia]. }
  assert (LKc3 : LK0 ++ LK <> [] -> yb_state b' <> BS_ok /\ length (LK0 ++ LK) = 1%nat).
  { intros NE. destruct LK0 as [|k0 LK0'].
    - cbn [app] in *. destruct (LKc NE) as [SB L1]. split; [| exact L1]. intros OK'. apply SB. exact (proj1 (APok OK')).
    - destruct (LKB3 ltac:(discriminate)) as [SB' L1]. specialize (NLK ltac:(discriminate)).
      destruct LK as [|k LK']; [rewrite app_nil_r; split; [exact SB'| exact L1]|].
      exfalso. destruct (LKc ltac:(discriminate)) as [SB _]. exact (SB NLK). }
  assert (OSB3' : oshadow m3 (mb_addr mb') SIZEOF_BUF) by exact OS3.
  clear PRES12 PRES3 MI2 ST2 TXT2 BR2 OSB2 OSD2 AHK2 YS2 LKc LKB3 NLK MU2 WM2 UB2 UB1.
  (* [comment removed for export] *)
  arz_seg KIPY AHK3.
  pose proof (aypol_ffshadow Y _ ((0, FF) :: LF) _ _ LINK (0, FF) (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) as PFFS.
  eapply evtA_cut.
  { eapply (seg_latch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SQ FF B S n e2 p); [exact MI3| exact FSH3| lia| aceil; lia| exact FFal| lia| lia| exact N26| exact E2R| exact PFFS]. }
  cbv beta. intros ms4 (xl & m4 & MI4 & MU4 & WM4 & FSH4 & CASES).
  assert (STEP : forall mo4, magree mo3 mo4 -> LI (y_aS Y s3') (y_aN Y s3') (y_aEB Y s3') mo4 -> m_halted mo4 = None ->
            exists (AHK4 : y_AHK Y s3' (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST) ((0, FF) :: LF) m4 mo4), y_ayR Y s3' mo3 s3' mo4).
  { intros mo4 Hag4 HLI4 Hh4. destruct (BACK mo4 Hag4 HLI4) as [AHKb R4].
    eexists; [| exact R4]. eapply FRAMEY; [exact AHKb| exact MU4| exact WM4|].
    constructor; [right; right; right; left; exists (0, FF); split; [left; reflexivity| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia]| constructor]. }
  pose proof (aystatics_munch _ _ _ YS3 MU4 WM4 ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS4.
  assert (PRES34 : ay_pres (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST) LF (bv_unsigned sp) [] m3 m4).
  { eapply ay_pres_of_munch; [exact MU4| exact WM4|]. intros a Ha Hc _. apply outside_cons; [| exact I].
    eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ _ LF (bv_unsigned sp) (0, FF)); [exact AHK3| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| right; cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia| lia| aceil; lia| exact Hc]. }
  assert (PRES4 : ay_pres REST LF (bv_unsigned sp) [] m m4).
  { eapply ay_pres_trans; [exact PRES3w|]. eapply (ay_pres_weaken Y); [exact PRES34| lia| exact INR3| intros f Hf; exact Hf| auto]. }
  Ltac tr34 H MU4 WM4 := eapply (rw_cells_transport bsegs) in H; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; first [lia| aceil; lia]].
  unfold dspill in FRQ3. unfold dsaved in SV3.
  tr34 FRQ3 MU4 WM4. tr34 SV3 MU4 WM4. tr34 FFA3 MU4 WM4. tr34 U53 MU4 WM4. tr34 FJ3 MU4 WM4. tr34 FFP3 MU4 WM4.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES34 YAF3 ltac:(destruct AFIN as (ba & Hba & A1 & A2 & _); exists ba; split; [apply INR3; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB A1 A2; Z.div_mod_to_equations; lia)) as YAF4.
  eapply (stk_transport_disjoint bsegs) in GAP3; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint bsegs) in ST3; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; lia].
  pose proof (txt_pres _ _ _ _ _ PRES34 INR3 TXT3) as TXT4.
  assert (BR4 : buf_rep bsegs m4 mb' b' AF).
  { eapply (buf_rep_agree bsegs); [eapply ay_pres_agree; exact PRES34| exact BR3| |].
    - intros a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_addr mb') SIZEOF_BUF). split; [unfold buf_blocks; left; reflexivity| cbn; lia].
    - intros Hd a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_data mb') (yb_len b')).
      split; [unfold buf_blocks; destruct (yb_data b'); [right; left; reflexivity| exfalso; apply Hd; reflexivity]| cbn; lia]. }
  apply evtA_done. intros mo4 Hag4 HLI4 Hh4. destruct (STEP mo4 Hag4 HLI4 Hh4) as [AHK4 R4]. clear STEP LINK BACK PFFS.
  assert (OSB4 : oshadow m4 (mb_addr mb') SIZEOF_BUF).
  { destruct (BSHY _ _ _ _ _ (mkABlock (mb_addr mb') SIZEOF_BUF) AHK4 ltac:(unfold buf_blocks; left; reflexivity) ltac:(cbn; unfold SIZEOF_BUF; lia)) as [X _]. exact X. }
  assert (OSD4 : yb_data b' <> None -> oshadow m4 (mb_data mb') (yb_len b') /\ amem (mb_data mb') (yb_len b')).
  { intros Hd. destruct (OSD3 Hd) as [OD HI]. split; [| exact HI]. destruct (Z.lt_ge_cases 0 (yb_len b')) as [POS|Z0].
    - destruct (BSHY _ _ _ _ _ (mkABlock (mb_data mb') (yb_len b')) AHK4 ltac:(unfold buf_blocks; destruct (yb_data b'); [right; left; reflexivity| exfalso; apply Hd; reflexivity]) POS) as [X _]. exact X.
    - destruct OD as (D8 & Dn & DU). split; [exact D8|]. split; [exact Dn|].
      eapply (u8arr_transport bsegs); [exact DU| exact MU4| exact WM4|]. rewrite (blk_shadow_length (yb_len b')) by lia.
      cbv [disjoint_from fst snd]. clear -CEILB Z0 D8 Dn. Z.div_mod_to_equations. lia. }
  destruct CASES as [[LT ->]| [EQ ->]]. all: unfold DST.
  - (* [comment removed for export] *)
    eapply (HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m4 mo4 s3' b' mb' (LK0 ++ LK) (p + 1) (p + 1));
      [ rewrite <- app_assoc; exact AHK4 | exact YS4 | exact MI4 | exact ST3 | exact GAP3 | exact FRM3
      | exact FRQ3 | exact SV3 | exact FFA3 | exact U53 | exact FJ3 | exact FFP3 | exact FSH4 | exact TXT4
      | exact YAF4 | exact BR4 | exact BI' | unfold mb_same in *; congruence | exact OSB4 | exact OSD4
      | exact PRES4 | eapply RRT; [exact R1|]; eapply RRT; [exact R2|]; eapply RRT; [exact R3| exact R4] | rewrite SO3; exact SO1 | exact CRED3 | exact RR0
      | exact LKc3 | lk0 | exact UB' | lia | lia | exact SBP | lia
      | intros r Hr; apply HL; eapply yleaf_bind; [exact YLA| exact Hr] ].
  - (* [comment removed for export] *)
    pose proof (sub_chunk m4 _ [] [C8 wf0] [C8 wf8; C8 wf16; CB 8 j24] ltac:(exact FFA3)) as FF04. cbn [cells_size csize Nat.add Z.of_nat] in FF04. rewrite Z.add_0_r in FF04.
    pose proof (sub_chunk m4 _ [C8 w0; C8 (Z_to_bv 64 1047552); C8 (Z_to_bv 64 (FF + 32)); C8 (Z_to_bv 64 55296); C8 (Z_to_bv 64 64512);
                                 C8 (Z_to_bv 64 A_LIT_BS); C8 (Z_to_bv 64 A_LIT_BSL); C8 (Z_to_bv 64 A_LIT_SL); C8 (Z_to_bv 64 A_LIT_QT); C8 (Z_to_bv 64 A_LIT_CR)]
                   [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] [C8 w96; C8 (Z_to_bv 64 FF); C4 sur; C4 cp] ltac:(exact FRQ3)) as L112. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in L112.
    unfold fsh_out, F1b, F3b, F8b in FSH4.
    eapply (dec_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m4 mo4 s3' b' mb' (LK0 ++ LK) (p + 1) (p + 1));
      [ rewrite <- app_assoc; exact AHK4 | exact YS4 | exact MI4 | exact ST3 | exact GAP3 | exact FRM3
      | exact FRQ3 | reflexivity | exact L112 | exact SV3 | exact FF04 | exact FFP3 | exact FSH4 | exact TXT4
      | exact YAF4 | exact BR4 | exact BI' | unfold mb_same in *; congruence | exact OSB4 | exact OSD4
      | exact PRES4 | eapply RRT; [exact R1|]; eapply RRT; [exact R2|]; eapply RRT; [exact R3| exact R4] | rewrite SO3; exact SO1 | exact CRED3 | exact RR0
      | exact LKc3 | lk0 | exact UB' | lia | lia
      | intros bf Hbf; eapply exit_leaf; [| exact Hbf]; apply HL; eapply yleaf_bind; [exact YLA|];
        destruct f' as [|f'']; [exfalso; lia|]; apply dlf_exit; lia ].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dec_u8 : forall f', head_ok f' ->
  forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (b1 : ybuf) (mb1 : mbuf) (LK : list ablock) (p e2 cp : Z)
    (w0 w96 sur cpw : word) (ubs : list byte) (wf0 wf8 wf16 : word) (j24 j37 : list byte),
  y_AHK Y s1' (abl (buf_blocks mb1 b1) ++ LK ++ REST) ((0, FF) :: LF) m1 mo1 -> aystatics m1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 120) (bv_unsigned sp + -104) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ (dspill w0 w96 FF sur cpw) ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) dsaved ->
  rw_cells bsegs m1 FF [C8 wf0; C8 wf8; C8 wf16; CB 8 j24] -> rw_cells bsegs m1 (FF + 32) [CB 5 (u8out cp ubs)] -> length ubs = 5%nat -> rw_cells bsegs m1 (FF + 37) [CB 19 j37] ->
  rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 (y_aflag Y 0 FF))] ->
  rw_cells bsegs m1 (FF / 8 + 2147450880) fsh_in ->
  bytes_at bsegs m1 S (zbytes str) ->
  rw_cells bsegs m1 AF (alloc_cells ayc) -> buf_rep bsegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 ->
  oshadow m1 (mb_addr mb1) SIZEOF_BUF -> (yb_data b1 <> None -> oshadow m1 (mb_data mb1) (yb_len b1) /\ amem (mb_data mb1) (yb_len b1)) ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s -> y_phi_buf Y b1 + RR <= y_acredit Y s1' -> 0 <= RR ->
  (LK <> [] -> yb_state b1 <> BS_ok /\ length LK = 1%nat) -> LK = [] ->
  0 < cp < 2097152 ->
  yb_used b1 + zlength (RY_decode1.u8enc cp) <= p + 1 -> 0 <= p -> p + 1 <= n -> sbody_ix str (p + 1) n -> (Z.to_nat (n - p) <= f')%nat -> 0 <= e2 < 2^32 ->
  (forall r, yleaf (b2 <- ybuf_append b1 (RY_decode1.u8enc cp) ;; ydecode_loop f' b2 str n (p + 1) (p + 1)) r -> yleaf WHOLE r) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 e2) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 p) t3 t4 t5 t6)
                          F1 (Z_to_bv 64 ADP_TAIL) fc1 None m1 (seg_rom bsegs)) mo1) K.
Proof. aceil.
  intros f' HEAD. intros until j37.
  intros AHK1 YS1 MI1 ST1 GAP1 FRM1 FRQ SV1 FFA U5 LU5 FJ FFP FSH TXT1 YAF1 BR1 BI MBS OSB1 OSD1 PRES1 R1 SO1 CRED1 RR0 LKc ELK CPR HUSED P0 PN SBP HF E2R HL.
  destruct (u8enc_facts cp CPR) as [UF UL].
  set (us := RY_decode1.u8enc cp) in *.
  assert (UF' : Forall (fun c => 0 <= c < 256) us) by (eapply Forall_impl; [| exact UF]; cbv beta; intros; lia).
  assert (UNZ : ~ In 0 us) by (intros HI; rewrite Forall_forall in UF; specialize (UF 0 HI); lia).
  assert (LJ : length j37 = 19%nat) by (destruct FJ as [[WF _] _]; cbn in WF; tauto).
  assert (E8F : FF mod 8 = 0) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof (length_u8out cp ubs LU5 UL) as LO5. fold us in LO5.
  assert (UB : bytes_at bsegs m1 (FF + 32) (zbytes (us ++ 0 :: (map bv_unsigned (skipn (Datatypes.S (length us)) ubs ++ firstn 3 j37))))).
  { rewrite zbytes_app. cbn [zbytes map app]. change (map (Z_to_bv 8) (map bv_unsigned ?l)) with (zbytes (map bv_unsigned l)). rewrite zbytes_unbytes.
    change (map (Z_to_bv 8) us ++ Z_to_bv 8 0 :: skipn (Datatypes.S (length us)) ubs ++ firstn 3 j37) with (zbytes us ++ (Z_to_bv 8 0 :: skipn (Datatypes.S (length us)) ubs) ++ firstn 3 j37).
    rewrite app_comm_cons, app_assoc. apply bytes_at_app. split.
    - destruct U5 as [[_ B5] _]. cbn [cells_bytes cbytes] in B5. rewrite app_nil_r in B5. unfold u8out in B5. fold us in B5. exact B5.
    - rewrite length_app, zbytes_length. cbn [length]. rewrite length_skipn, LU5.
      replace (FF + 32 + Z.of_nat (length us + Datatypes.S (5 - Datatypes.S (length us)))) with (FF + 37) by lia.
      destruct FJ as [[_ BJ] _]. cbn [cells_bytes cbytes] in BJ. rewrite app_nil_r in BJ.
      rewrite <- (firstn_skipn 3 j37) in BJ. apply bytes_at_app in BJ. exact (proj1 BJ). }
  eapply (dec_tail f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 mo1 s1' b1 mb1 LK p e2 (FF + 32) us (map bv_unsigned (skipn (Datatypes.S (length us)) ubs ++ firstn 3 j37)));
    try eassumption.
  - apply Forall_app. split; [exact UF'|]. apply Forall_cons; [lia| apply RY_decode1.Forall_unbytes].
  - unfold zlength. rewrite length_map, length_app, length_skipn, length_firstn, LU5, LJ. clear -CEILB UL E8F. Z.div_mod_to_equations. lia.
  - unfold zlength. rewrite length_map, length_app, length_skipn, length_firstn, LU5, LJ. lia.
  - right. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma dec_nul : forall f', head_ok f' ->
  forall (rav t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (b1 : ybuf) (mb1 : mbuf) (LK : list ablock) (e : Z)
    (w0 w96 sur cpw : word) (ubs : list byte) (wf0 wf8 wf16 : word) (j24 j37 : list byte),
  y_AHK Y s1' (abl (buf_blocks mb1 b1) ++ LK ++ REST) ((0, FF) :: LF) m1 mo1 -> aystatics m1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 120) (bv_unsigned sp + -104) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ (dspill w0 w96 FF sur cpw) ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) dsaved ->
  rw_cells bsegs m1 FF [C8 wf0; C8 wf8; C8 wf16; CB 8 j24] -> rw_cells bsegs m1 (FF + 32) [CB 5 (u8out 0 ubs)] -> length ubs = 5%nat -> rw_cells bsegs m1 (FF + 37) [CB 19 j37] ->
  rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 (y_aflag Y 0 FF))] ->
  rw_cells bsegs m1 (FF / 8 + 2147450880) fsh_in ->
  bytes_at bsegs m1 S (zbytes str) ->
  rw_cells bsegs m1 AF (alloc_cells ayc) -> buf_rep bsegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 ->
  oshadow m1 (mb_addr mb1) SIZEOF_BUF -> (yb_data b1 <> None -> oshadow m1 (mb_data mb1) (yb_len b1) /\ amem (mb_data mb1) (yb_len b1)) ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s -> y_phi_buf Y b1 + RR <= y_acredit Y s1' -> 0 <= RR ->
  (LK <> [] -> yb_state b1 <> BS_ok /\ length LK = 1%nat) -> LK = [] ->
  yb_used b1 + 1 <= e + 6 -> 0 <= e -> e + 6 <= n -> sbody_ix str (e + 6) n -> (Z.to_nat (n - (e + 5)) <= f')%nat ->
  (forall r, yleaf (b2 <- ybuf_append b1 [0] ;; ydecode_loop f' b2 str n (e + 6) (e + 6)) r -> yleaf WHOLE r) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR (Z_to_bv 64 ADP_RET3) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 B) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                              (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (e + 5)) t3 t4 t5 t6)
                          F1 (Z_to_bv 64 AY_BUF_APPEND) fc1 None m1 (seg_rom bsegs)) mo1) K.
Proof. aceil.
  intros f' HEAD. intros until j37.
  intros AHK2 YS2 MI2 ST2 GAP1 FRM1 FRQ SV1 FFA U5 LU5 FJ FFP FSH TXT2 YAF1 BR2 BI MBS OSB2 OSD2 PRES1 R1 SO1 CRED1 RR0 LKc ELK HUSED P0 PN SBP HF HL.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof CEIL' as CE. pose proof LO' as LOx. pose proof (zlength_nonneg str) as NL0.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  assert (E8F : FF = 8 * (FF / 8)) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  assert (EB : mb_addr mb1 = B) by (unfold B; exact MBS).
  assert (INR : forall b0, In b0 REST -> In b0 (abl (buf_blocks mb1 b1) ++ LK ++ REST)) by (intros b0 Hb0; apply in_or_app; right; apply in_or_app; right; exact Hb0).
  assert (UB1 : bytes_at bsegs m1 (FF + 32) (zbytes [0])).
  { destruct U5 as [[_ B5] _]. cbn [cells_bytes cbytes] in B5. rewrite app_nil_r in B5. unfold u8out in B5.
    rewrite (proj2 (proj2 (bytes_at_app bsegs m1 (FF + 32) (zbytes (RY_decode1.u8enc 0)) _)) ) in B5 || idtac.
    apply bytes_at_app in B5. exact (proj1 B5). }
  pose proof PRES1 as PRES12w.
  (* [comment removed for export] *)
  pose proof (sub_chunk m1 _ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV1)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV16 by lia.
  unfold AY_BUF_APPEND.
  eapply (BAPP2 ((0, FF) :: LF) (LK ++ REST) mb1 b1 AF (FF + 32) [0] lo RR K);
    [ ba_app EB ltac:(lia)
    | exact K0
    | apply AYST_split; split; [exact AHK2| exact YS2]
    | exact BR2 | exact BI | exact YAF1
    | eapply yaf_ok_now; [exact AHK2| exact INR| intros b0 Hb0; apply in_or_app; right; exact Hb0]
    | exact OSB2
    | intros Hd; exact (proj1 (OSD2 Hd))
    | exact UB1
    | apply Forall_cons; [lia| apply Forall_nil]
    | intros _; lia
    | replace (zlength [0]) with 1 by reflexivity; aceil; lia
    | replace (zlength [0]) with 1 by reflexivity; lia
    | (* [comment removed for export] *) unfold ysrc_range; right; right; left; exists (0, FF); split; [left; reflexivity| cbn [fst snd]; rewrite ff_bytes_0; replace (zlength [0]) with 1 by reflexivity; lia]
    | (* [comment removed for export] *) unfold ysrc_win; rewrite USQ; intros Hn s' LBx m' mo' AHK' PRES';
      destruct (KIPY _ _ _ _ _ AHK') as (_ & _ & _ & LINK' & _); unfold fsh_in in FSH;
      pose proof (aypres_fframe _ _ _ _ _ _ _ (0, FF) PRES' FSH (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) as FSH';
      unfold F1b, F3b in FSH'; replace (zlength [0]) with 1 by reflexivity; destruct (u5_window m' FF 1 _ _ _ _ _ _ _ FFal ltac:(lia) ltac:(lia) FSH') as (SW' & RC' & WL' & WH');
      eexists; split; [exact SW'|]; split; [exact RC'|]; rewrite WL', WH';
      eapply (aypol_ffshadow Y _ ((0, FF) :: LF) _ _ LINK' (0, FF)); [left; reflexivity| cbn [snd]; unfold oshw_lo, A_SB; lia| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia| lia| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia]
    | unfold ayframe_pre, AY_BUF_APPEND_STACK, AMALLOC_STACK; aceil; rewrite USQ;
      split; [exact ST2|]; split; [lia|]; split; [unfold AY_DECODE_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK in LO; lia|]; split; [lia|];
      split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|]; split; [exact MI2|]; split; [exact TP| exact FRM1]
    | rewrite EB; reflexivity | reflexivity | reflexivity
    | exact CRED1 | exact RR0
    | rewrite nbig_app2; pose proof (nbig_le_len2 LK); destruct LK; [cbn in *; lia| destruct (LKc ltac:(discriminate)) as [_ L1]; cbn [length] in *; lia]
    | rewrite USQ; eapply USTEP; [unfold ADP_RET3; rewrite unsigned_lit by lia; exact URA_a2| lia| exact SV16
      | eapply UFRAME; [| exact UA]; intros a Ha;
        destruct (PRES1 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E1 _]; exact E1]
    | ].
  cbv beta. intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c F3 fc3 m3 mo3 s3' b' mb' LK0 POST.
  destruct POST as (SO3 & R3 & CRED3 & (MI3 & ST3 & FRM3 & _ & PRES3) & YAF3 & YLA & BR3 & MBS3 & OS3 & OSD3 & LKZ3 & AY3 & LKB3 & NLK).
  rewrite USQ in ST3, PRES3.
  replace (ret_pc (Z_to_bv 64 ADP_RET3)) with (Z_to_bv 64 ADP_RET3) by (symmetry; apply ret_pc_even; [unfold ADP_RET3; lia| reflexivity]).
  apply AYST_split in AY3. destruct AY3 as [AHK3 YS3].
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 SV1 ltac:(lia)) as SV3. clear SV1 SV16.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 FRQ ltac:(lia)) as FRQ3. clear FRQ.
  assert (GAP3 : stk bsegs m3 (SQ + 120) (bv_unsigned sp + -104)).
  { eapply stk_agree; [eapply ay_pres_agree; exact PRES3| exact GAP1| intros a Ha; split; [left; lia| intros F0; exact F0]]. }
  clear GAP1.
  trff FFA PRES3 FF. trff U5 PRES3 FF. trff FJ PRES3 FF. trff FFP PRES3 FF. unfold fsh_in in FSH. trff FSH PRES3 FF.
  clear FFA U5 FJ FFP FSH. rename H into FFA3. rename H0 into U53. rename H1 into FJ3. rename H2 into FFP3. rename H3 into FSH3.
  pose proof (txt_pres _ _ _ _ _ PRES3 ltac:(intros b0 Hb0; apply in_or_app; right; exact Hb0) TXT2) as TXT3.
  assert (PRES3w : ay_pres REST LF (bv_unsigned sp) [] m m3).
  { eapply ay_pres_trans; [exact PRES1|].
    eapply (ay_pres_weaken Y); [exact PRES3| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0| intros f Hf; right; exact Hf| auto]. }
  assert (INR3 : forall b0, In b0 REST -> In b0 (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST)).
  { intros b0 Hb0. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hb0. }
  pose proof (ypost_yleaf _ _ _ (ybuf_append_post2 b1 [0] BI ltac:(replace (zlength [0]) with 1 by reflexivity; lia)) YLA) as AP. cbv beta in AP. destruct AP as (BI' & APok & APerr).
  assert (UB' : yb_used b' <= e + 6).
  { destruct (yb_state b') eqn:EST; [destruct (APok eq_refl) as (_ & -> & _); replace (zlength [0]) with 1 by reflexivity; lia| destruct (APerr ltac:(discriminate)) as [-> _]; lia| destruct (APerr ltac:(discriminate)) as [-> _]; lia]. }
  assert (LKc3 : LK0 ++ LK <> [] -> yb_state b' <> BS_ok /\ length (LK0 ++ LK) = 1%nat).
  { intros NE. destruct LK0 as [|k0 LK0'].
    - cbn [app] in *. destruct (LKc NE) as [SB L1]. split; [| exact L1]. intros OK'. apply SB. exact (proj1 (APok OK')).
    - destruct (LKB3 ltac:(discriminate)) as [SB' L1]. specialize (NLK ltac:(discriminate)).
      destruct LK as [|k LK']; [rewrite app_nil_r; split; [exact SB'| exact L1]|].
      exfalso. destruct (LKc ltac:(discriminate)) as [SB _]. exact (SB NLK). }
  assert (OSB3' : oshadow m3 (mb_addr mb') SIZEOF_BUF) by exact OS3.
  clear PRES3 MI2 ST2 TXT2 BR2 OSB2 OSD2 AHK2 YS2 LKc LKB3 NLK UB1.
  (* [comment removed for export] *)
  arz_seg KIPY AHK3.
  pose proof (aypol_ffshadow Y _ ((0, FF) :: LF) _ _ LINK (0, FF) (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) as PFFS.
  eapply evtA_cut.
  { eapply (seg_latch0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SQ FF B S n e (e + 5)); [exact MI3| exact FSH3| lia| aceil; lia| exact FFal| lia| lia| exact N26| lia| exact PFFS]. }
  cbv beta. intros ms4 (xl & m4 & MI4 & MU4 & WM4 & FSH4 & CASES).
  assert (STEP : forall mo4, magree mo3 mo4 -> LI (y_aS Y s3') (y_aN Y s3') (y_aEB Y s3') mo4 -> m_halted mo4 = None ->
            exists (AHK4 : y_AHK Y s3' (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST) ((0, FF) :: LF) m4 mo4), y_ayR Y s3' mo3 s3' mo4).
  { intros mo4 Hag4 HLI4 Hh4. destruct (BACK mo4 Hag4 HLI4) as [AHKb R4].
    eexists; [| exact R4]. eapply FRAMEY; [exact AHKb| exact MU4| exact WM4|].
    constructor; [right; right; right; left; exists (0, FF); split; [left; reflexivity| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia]| constructor]. }
  pose proof (aystatics_munch _ _ _ YS3 MU4 WM4 ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS4.
  assert (PRES34 : ay_pres (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST) LF (bv_unsigned sp) [] m3 m4).
  { eapply ay_pres_of_munch; [exact MU4| exact WM4|]. intros a Ha Hc _. apply outside_cons; [| exact I].
    eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ _ LF (bv_unsigned sp) (0, FF)); [exact AHK3| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| right; cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia| lia| aceil; lia| exact Hc]. }
  assert (PRES4 : ay_pres REST LF (bv_unsigned sp) [] m m4).
  { eapply ay_pres_trans; [exact PRES3w|]. eapply (ay_pres_weaken Y); [exact PRES34| lia| exact INR3| intros f Hf; exact Hf| auto]. }
  unfold dspill in FRQ3. unfold dsaved in SV3.
  tr34 FRQ3 MU4 WM4. tr34 SV3 MU4 WM4. tr34 FFA3 MU4 WM4. tr34 U53 MU4 WM4. tr34 FJ3 MU4 WM4. tr34 FFP3 MU4 WM4.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES34 YAF3 ltac:(destruct AFIN as (ba & Hba & A1 & A2 & _); exists ba; split; [apply INR3; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB A1 A2; Z.div_mod_to_equations; lia)) as YAF4.
  eapply (stk_transport_disjoint bsegs) in GAP3; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint bsegs) in ST3; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; lia].
  pose proof (txt_pres _ _ _ _ _ PRES34 INR3 TXT3) as TXT4.
  assert (BR4 : buf_rep bsegs m4 mb' b' AF).
  { eapply (buf_rep_agree bsegs); [eapply ay_pres_agree; exact PRES34| exact BR3| |].
    - intros a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_addr mb') SIZEOF_BUF). split; [unfold buf_blocks; left; reflexivity| cbn; lia].
    - intros Hd a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_data mb') (yb_len b')).
      split; [unfold buf_blocks; destruct (yb_data b'); [right; left; reflexivity| exfalso; apply Hd; reflexivity]| cbn; lia]. }
  apply evtA_done. intros mo4 Hag4 HLI4 Hh4. destruct (STEP mo4 Hag4 HLI4 Hh4) as [AHK4 R4]. clear STEP LINK BACK PFFS.
  assert (OSB4 : oshadow m4 (mb_addr mb') SIZEOF_BUF).
  { destruct (BSHY _ _ _ _ _ (mkABlock (mb_addr mb') SIZEOF_BUF) AHK4 ltac:(unfold buf_blocks; left; reflexivity) ltac:(cbn; unfold SIZEOF_BUF; lia)) as [X _]. exact X. }
  assert (OSD4 : yb_data b' <> None -> oshadow m4 (mb_data mb') (yb_len b') /\ amem (mb_data mb') (yb_len b')).
  { intros Hd. destruct (OSD3 Hd) as [OD HI]. split; [| exact HI]. destruct (Z.lt_ge_cases 0 (yb_len b')) as [POS|Z0].
    - destruct (BSHY _ _ _ _ _ (mkABlock (mb_data mb') (yb_len b')) AHK4 ltac:(unfold buf_blocks; destruct (yb_data b'); [right; left; reflexivity| exfalso; apply Hd; reflexivity]) POS) as [X _]. exact X.
    - destruct OD as (D8 & Dn & DU). split; [exact D8|]. split; [exact Dn|].
      eapply (u8arr_transport bsegs); [exact DU| exact MU4| exact WM4|]. rewrite (blk_shadow_length (yb_len b')) by lia.
      cbv [disjoint_from fst snd]. clear -CEILB Z0 D8 Dn. Z.div_mod_to_equations. lia. }
  destruct CASES as [[LT ->]| [EQ ->]]. all: unfold DST.
  - (* [comment removed for export] *)
    eapply (HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m4 mo4 s3' b' mb' (LK0 ++ LK) (e + 6) (e + 6));
      [ rewrite <- app_assoc; exact AHK4 | exact YS4 | exact MI4 | exact ST3 | exact GAP3 | exact FRM3
      | exact FRQ3 | exact SV3 | exact FFA3 | exact U53 | exact FJ3 | exact FFP3 | exact FSH4 | exact TXT4
      | exact YAF4 | exact BR4 | exact BI' | unfold mb_same in *; congruence | exact OSB4 | exact OSD4
      | exact PRES4 | eapply RRT; [exact R1|]; eapply RRT; [exact R3| exact R4] | rewrite SO3; exact SO1 | exact CRED3 | exact RR0
      | exact LKc3 | lk0 | exact UB' | lia | lia | exact SBP | lia
      | intros r Hr; apply HL; eapply yleaf_bind; [exact YLA| exact Hr] ].
  - (* [comment removed for export] *)
    pose proof (sub_chunk m4 _ [] [C8 wf0] [C8 wf8; C8 wf16; CB 8 j24] ltac:(exact FFA3)) as FF04. cbn [cells_size csize Nat.add Z.of_nat] in FF04. rewrite Z.add_0_r in FF04.
    pose proof (sub_chunk m4 _ [C8 w0; C8 (Z_to_bv 64 1047552); C8 (Z_to_bv 64 (FF + 32)); C8 (Z_to_bv 64 55296); C8 (Z_to_bv 64 64512);
                                 C8 (Z_to_bv 64 A_LIT_BS); C8 (Z_to_bv 64 A_LIT_BSL); C8 (Z_to_bv 64 A_LIT_SL); C8 (Z_to_bv 64 A_LIT_QT); C8 (Z_to_bv 64 A_LIT_CR)]
                   [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] [C8 w96; C8 (Z_to_bv 64 FF); C4 sur; C4 cpw] ltac:(exact FRQ3)) as L112. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in L112.
    unfold fsh_out, F1b, F3b, F8b in FSH4.
    eapply (dec_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m4 mo4 s3' b' mb' (LK0 ++ LK) (e + 6) (e + 6));
      [ rewrite <- app_assoc; exact AHK4 | exact YS4 | exact MI4 | exact ST3 | exact GAP3 | exact FRM3
      | exact FRQ3 | reflexivity | exact L112 | exact SV3 | exact FF04 | exact FFP3 | exact FSH4 | exact TXT4
      | exact YAF4 | exact BR4 | exact BI' | unfold mb_same in *; congruence | exact OSB4 | exact OSD4
      | exact PRES4 | eapply RRT; [exact R1|]; eapply RRT; [exact R3| exact R4] | rewrite SO3; exact SO1 | exact CRED3 | exact RR0
      | exact LKc3 | lk0 | exact UB' | lia | lia
      | intros bf Hbf; eapply exit_leaf; [| exact Hbf]; apply HL; eapply yleaf_bind; [exact YLA|];
        destruct f' as [|f'']; [exfalso; lia|]; apply dlf_exit; lia ].
Qed.

Ltac trw H MU WM := eapply (rw_cells_transport bsegs) in H; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; first [lia| aceil; lia]].

(* [comment removed for export] *)
Lemma dec_cp : forall f', head_ok f' ->
  forall (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (b1 : ybuf) (mb1 : mbuf) (LK : list ablock) (e cp : Z)
    (w0 w96 sur cpw : word) (ubs : list byte) (wf0 wf8 wf16 : word) (j24 j37 : list byte),
  y_AHK Y s1' (abl (buf_blocks mb1 b1) ++ LK ++ REST) ((0, FF) :: LF) m1 mo1 -> aystatics m1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 120) (bv_unsigned sp + -104) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ (dspill w0 w96 FF sur cpw) ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) dsaved ->
  rw_cells bsegs m1 FF [C8 wf0; C8 wf8; C8 wf16; CB 8 j24] -> rw_cells bsegs m1 (FF + 32) [CB 5 ubs] -> length ubs = 5%nat -> rw_cells bsegs m1 (FF + 37) [CB 19 j37] ->
  rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 (y_aflag Y 0 FF))] ->
  rw_cells bsegs m1 (FF / 8 + 2147450880) fsh_in ->
  bytes_at bsegs m1 S (zbytes str) ->
  rw_cells bsegs m1 AF (alloc_cells ayc) -> buf_rep bsegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 ->
  oshadow m1 (mb_addr mb1) SIZEOF_BUF -> (yb_data b1 <> None -> oshadow m1 (mb_data mb1) (yb_len b1) /\ amem (mb_data mb1) (yb_len b1)) ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s -> y_phi_buf Y b1 + RR <= y_acredit Y s1' -> 0 <= RR ->
  (LK <> [] -> yb_state b1 <> BS_ok /\ length LK = 1%nat) -> LK = [] ->
  0 <= cp < 65536 ->
  yb_used b1 + 4 <= e + 6 -> 0 <= e -> e + 6 <= n -> sbody_ix str (e + 6) n -> (Z.to_nat (n - (e + 5)) <= f')%nat ->
  (forall r, yleaf (b2 <- ybuf_append b1 (RY_decode1.u8enc cp) ;; ydecode_loop f' b2 str n (e + 6) (e + 6)) r -> yleaf WHOLE r) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 cp) a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) s7v (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (e + 5)) t3 t4 t5 t6)
                          F1 (Z_to_bv 64 ADP_CP) fc1 None m1 (seg_rom bsegs)) mo1) K.
Proof. aceil.
  intros f' HEAD. intros until j37.
  intros AHK1 YS1 MI1 ST1 GAP1 FRM1 FRQ SV1 FFA U5 LU5 FJ FFP FSH TXT1 YAF1 BR1 BI MBS OSB1 OSD1 PRES1 R1 SO1 CRED1 RR0 LKc ELK CPR HUSED E0 EN SBP HF HL.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof CEIL' as CE. pose proof LO' as LOx. pose proof (zlength_nonneg str) as NL0.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof FFce as FC. aceil.
  assert (INR : forall b0, In b0 REST -> In b0 (abl (buf_blocks mb1 b1) ++ LK ++ REST)) by (intros b0 Hb0; apply in_or_app; right; apply in_or_app; right; exact Hb0).
  arz_seg KIPY AHK1.
  pose proof (aypol_fframe Y _ ((0, FF) :: LF) _ _ LINK (0, FF) FF (FF + 64) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; rewrite ff_bytes_0; lia) ltac:(lia) ltac:(cbn; rewrite ff_bytes_0; lia)) as PFF.
  pose proof (aypol_ffshadow Y _ ((0, FF) :: LF) _ _ LINK (0, FF) (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) as PFFS.
  pose proof (aypol_stack Y _ ((0, FF) :: LF) _ _ LINK SQ (SQ + 120) ltac:(aceil; lia) ltac:(lia)) as PSQ.
  eapply evtA_cut.
  { eapply (seg_cp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ubs F1 fc1 m1 SQ FF B S n e cp);
      [exact MI1| exact FRQ| lia| lia| exact U5| exact FSH| lia| exact FC| exact FFal| exact CPR| pose proof (proj1 TXT1); lia| exact PSQ| exact PFF| exact PFFS]. }
  cbv beta. intros ms2 (x0 & x1 & x2 & x3 & m2 & MU2 & WM2 & MI2 & U52 & FRQ2 & FSH2 & CASES). clear FRQ U5 FSH.
  apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHKb R2]. clear LINK BACK PFF PFFS PSQ.
  destruct (own_writes _ _ _ _ _ _ AHKb MU2 WM2 ltac:(repeat (constructor; [split; [cbn; lia| cbn [fst snd]; lia]|]); constructor)) as (AHK2 & PRES12 & YSf).
  pose proof (YSf YS1) as YS2. clear YSf AHKb.
  unfold dsaved in SV1. trw SV1 MU2 WM2. trw FFA MU2 WM2. trw FJ MU2 WM2. trw FFP MU2 WM2. fold dsaved in SV1.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES12 YAF1 ltac:(destruct AFIN as (ba & Hba & A1 & A2 & _); exists ba; split; [apply INR; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB A1 A2; Z.div_mod_to_equations; lia)) as YAF2.
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint bsegs) in ST1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
  pose proof (txt_pres _ _ _ _ _ PRES12 INR TXT1) as TXT2.
  destruct (buf_keep _ _ _ _ _ _ _ _ AHK2 PRES12 BR1 OSD1) as (BR2 & OSB2 & OSD2).
  assert (PRES2 : ay_pres REST LF (bv_unsigned sp) [] m m2).
  { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES12| lia| exact INR| intros f Hf; exact Hf| auto]. }
  clear MI1 TXT1 YAF1 BR1 OSB1 OSD1 AHK1 YS1 PRES1.
  pose proof (u8enc_facts) as UFC.
  destruct CASES as [[NZ ->]| [-> ->]].
  - change ADP_T0 with ADP_TAIL.
    eapply (dec_u8 f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m2 mo2 s1' b1 mb1 LK (e + 5) e cp); try eassumption; try lia.
    + eapply RRT; [exact R1| exact R2].
    + destruct (u8enc_facts cp ltac:(lia)) as [_ UL]. unfold zlength. lia.
    + replace (e + 5 + 1) with (e + 6) by lia. exact SBP.
    + replace (e + 5 + 1) with (e + 6) by lia. exact HL.
  - eapply (dec_nul f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m2 mo2 s1' b1 mb1 LK e); try eassumption; try lia.
    eapply RRT; [exact R1| exact R2].
  Unshelve. all: exact (Z_to_bv 64 0).   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma dec_4 : forall f', head_ok f' ->
  forall (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (b1 : ybuf) (mb1 : mbuf) (LK : list ablock) (e cp : Z)
    (w0 w96 sur cpw : word) (ubs : list byte) (wf0 wf8 wf16 : word) (j24 j37 : list byte),
  y_AHK Y s1' (abl (buf_blocks mb1 b1) ++ LK ++ REST) ((0, FF) :: LF) m1 mo1 -> aystatics m1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 120) (bv_unsigned sp + -104) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ (dspill w0 w96 FF sur cpw) ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) dsaved ->
  rw_cells bsegs m1 FF [C8 wf0; C8 wf8; C8 wf16; CB 8 j24] -> rw_cells bsegs m1 (FF + 32) [CB 5 ubs] -> length ubs = 5%nat -> rw_cells bsegs m1 (FF + 37) [CB 19 j37] ->
  rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 (y_aflag Y 0 FF))] ->
  rw_cells bsegs m1 (FF / 8 + 2147450880) fsh_in ->
  bytes_at bsegs m1 S (zbytes str) ->
  rw_cells bsegs m1 AF (alloc_cells ayc) -> buf_rep bsegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 ->
  oshadow m1 (mb_addr mb1) SIZEOF_BUF -> (yb_data b1 <> None -> oshadow m1 (mb_data mb1) (yb_len b1) /\ amem (mb_data mb1) (yb_len b1)) ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s -> y_phi_buf Y b1 + RR <= y_acredit Y s1' -> 0 <= RR ->
  (LK <> [] -> yb_state b1 <> BS_ok /\ length LK = 1%nat) -> LK = [] ->
  65536 <= cp < 2097152 ->
  yb_used b1 + 4 <= e + 12 -> 0 <= e -> e + 12 <= n -> sbody_ix str (e + 12) n -> (Z.to_nat (n - (e + 11)) <= f')%nat ->
  (forall r, yleaf (b2 <- ybuf_append b1 (RY_decode1.u8enc cp) ;; ydecode_loop f' b2 str n (e + 12) (e + 12)) r -> yleaf WHOLE r) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 cp) a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (e + 11)) t3 t4 t5 t6)
                          F1 (Z_to_bv 64 ADP_J4) fc1 None m1 (seg_rom bsegs)) mo1) K.
Proof. aceil.
  intros f' HEAD. intros until j37.
  intros AHK1 YS1 MI1 ST1 GAP1 FRM1 FRQ SV1 FFA U5 LU5 FJ FFP FSH TXT1 YAF1 BR1 BI MBS OSB1 OSD1 PRES1 R1 SO1 CRED1 RR0 LKc ELK CPR HUSED E0 EN SBP HF HL.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof CEIL' as CE. pose proof LO' as LOx. pose proof (zlength_nonneg str) as NL0.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof FFce as FC. aceil.
  assert (INR : forall b0, In b0 REST -> In b0 (abl (buf_blocks mb1 b1) ++ LK ++ REST)) by (intros b0 Hb0; apply in_or_app; right; apply in_or_app; right; exact Hb0).
  arz_seg KIPY AHK1.
  pose proof (aypol_fframe Y _ ((0, FF) :: LF) _ _ LINK (0, FF) FF (FF + 64) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; rewrite ff_bytes_0; lia) ltac:(lia) ltac:(cbn; rewrite ff_bytes_0; lia)) as PFF.
  pose proof (aypol_ffshadow Y _ ((0, FF) :: LF) _ _ LINK (0, FF) (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) as PFFS.
  pose proof (aypol_stack Y _ ((0, FF) :: LF) _ _ LINK SQ (SQ + 120) ltac:(aceil; lia) ltac:(lia)) as PSQ.
  eapply evtA_cut.
  { eapply (seg_4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ubs F1 fc1 m1 SQ FF B S n e cp);
      [exact MI1| exact FRQ| lia| lia| exact U5| exact FSH| lia| exact FC| exact FFal| exact CPR| pose proof (proj1 TXT1); lia| exact PSQ| exact PFF| exact PFFS]. }
  cbv beta. intros ms2 (x0 & x1 & x2 & x3 & x4 & m2 & -> & MU2 & WM2 & MI2 & U52 & FRQ2 & FSH2). clear FRQ U5 FSH.
  apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHKb R2]. clear LINK BACK PFF PFFS PSQ.
  destruct (own_writes _ _ _ _ _ _ AHKb MU2 WM2 ltac:(repeat (constructor; [split; [cbn; lia| cbn [fst snd]; lia]|]); constructor)) as (AHK2 & PRES12 & YSf).
  pose proof (YSf YS1) as YS2. clear YSf AHKb.
  unfold dsaved in SV1. trw SV1 MU2 WM2. trw FFA MU2 WM2. trw FJ MU2 WM2. trw FFP MU2 WM2. fold dsaved in SV1.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES12 YAF1 ltac:(destruct AFIN as (ba & Hba & A1 & A2 & _); exists ba; split; [apply INR; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB A1 A2; Z.div_mod_to_equations; lia)) as YAF2.
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint bsegs) in ST1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
  pose proof (txt_pres _ _ _ _ _ PRES12 INR TXT1) as TXT2.
  destruct (buf_keep _ _ _ _ _ _ _ _ AHK2 PRES12 BR1 OSD1) as (BR2 & OSB2 & OSD2).
  assert (PRES2 : ay_pres REST LF (bv_unsigned sp) [] m m2).
  { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES12| lia| exact INR| intros f Hf; exact Hf| auto]. }
  clear MI1 TXT1 YAF1 BR1 OSB1 OSD1 AHK1 YS1 PRES1.
  change ADP_T0 with ADP_TAIL.
  eapply (dec_u8 f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m2 mo2 s1' b1 mb1 LK (e + 11) e cp); try eassumption; try lia.
  - eapply RRT; [exact R1| exact R2].
  - destruct (u8enc_facts cp ltac:(lia)) as [_ UL]. unfold zlength. lia.
  - replace (e + 11 + 1) with (e + 12) by lia. exact SBP.
  - replace (e + 11 + 1) with (e + 12) by lia. exact HL.
Qed.

(* [comment removed for export] *)
Lemma dec_uesc : forall f', head_ok f' ->
  forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (b0 b1 : ybuf) (mb1 : mbuf) (LK : list ablock) (beg e : Z)
    (w0 w96 sur cpw : word) (ubs : list byte) (wf0 wf8 wf16 : word) (j24 j37 : list byte),
  y_AHK Y s1' (abl (buf_blocks mb1 b1) ++ LK ++ REST) ((0, FF) :: LF) m1 mo1 -> aystatics m1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 120) (bv_unsigned sp + -104) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ (dspill w0 w96 FF sur cpw) ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) dsaved ->
  rw_cells bsegs m1 FF [C8 wf0; C8 wf8; C8 wf16; CB 8 j24] -> rw_cells bsegs m1 (FF + 32) [CB 5 ubs] -> length ubs = 5%nat -> rw_cells bsegs m1 (FF + 37) [CB 19 j37] ->
  rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 (y_aflag Y 0 FF))] ->
  rw_cells bsegs m1 (FF / 8 + 2147450880) fsh_in ->
  bytes_at bsegs m1 S (zbytes str) ->
  rw_cells bsegs m1 AF (alloc_cells ayc) -> buf_rep bsegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 ->
  oshadow m1 (mb_addr mb1) SIZEOF_BUF -> (yb_data b1 <> None -> oshadow m1 (mb_data mb1) (yb_len b1) /\ amem (mb_data mb1) (yb_len b1)) ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s -> y_phi_buf Y b1 + RR <= y_acredit Y s1' -> 0 <= RR ->
  (LK <> [] -> yb_state b1 <> BS_ok /\ length LK = 1%nat) -> LK = [] ->
  0 <= beg <= e -> e + 5 < n -> znth str e = 92 -> znth str (e + 1) = 117 ->
  (forall k, 0 <= k < 4 -> is_vhc (znth str (e + 2 + k)) = true) -> sbody_ix str (e + 6) n ->
  (Z.to_nat (n - e) < Datatypes.S f')%nat -> yb_used b1 <= e ->
  yleaf (ybuf_append b0 (zslice str beg (e - beg))) b1 ->
  (forall r, yleaf (ydecode_loop (Datatypes.S f') b0 str n beg e) r -> yleaf WHOLE r) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) s7v (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (e + 1)) t3 t4 t5 t6)
                          F1 (Z_to_bv 64 ADP_U) fc1 None m1 (seg_rom bsegs)) mo1) K.
Proof. aceil.
  intros f' HEAD. intros until j37.
  intros AHK1 YS1 MI1 ST1 GAP1 FRM1 FRQ SV1 FFA U5 LU5 FJ FFP FSH TXT1 YAF1 BR1 BI MBS OSB1 OSD1 PRES1 R1 SO1 CRED1 RR0 LKc ELK HBE E5 CB CU HHEX HREST HF UB HLB1 HL.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof CEIL' as CE. pose proof LO' as LOx. pose proof (zlength_nonneg str) as NL0.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof FFce as FC. aceil.
  assert (INR : forall b2, In b2 REST -> In b2 (abl (buf_blocks mb1 b1) ++ LK ++ REST)) by (intros b2 Hb2; apply in_or_app; right; apply in_or_app; right; exact Hb2).
  pose proof YS1 as (_ & _ & _ & STA1).
  destruct (txt_obj _ _ _ _ _ AHK1 INR ltac:(lia)) as (bt & INbt & OSBT & T1 & T2 & OH & TC & T0 & T8).
  destruct (sshadow_byte _ _ _ _ _ (SQ + 112) AHK1 ltac:(aceil; lia) ltac:(lia) ltac:(clear -CEILB SQ32; Z.div_mod_to_equations; lia)) as [SB0 (lo' & hi' & PB & PL1 & PL2 & PL3 & PL4)].
  replace (A_SB + (SQ + 112) / 8) with (A_SB + SQ / 8 + 14) in SB0, PL1, PL2 by (clear -CEILB SQ32; Z.div_mod_to_equations; lia).
  destruct (yhexToDigit_bound str (e + 2) HHEX) as (cp & HX & CPR).
  (* [comment removed for export] *)
  arz_seg KIPY AHK1.
  pose proof (aypol_stack Y _ ((0, FF) :: LF) _ _ LINK lo (SQ + 120) CEIL ltac:(lia)) as PSTKL.
  assert (PSSH : pol (acc_ok (m_vm_lazy mo1) (y_aS Y s1')) (A_SB + SQ / 8 + 14) (A_SB + SQ / 8 + 15)).
  { intros a k Ha Hk. eapply (aypol_pages _ _ lo' hi' PB PL3 PL4); lia. }
  pose proof (aypol_bshadow Y _ _ _ _ LINK bt (oshw_lo (ab_addr bt)) (oshw_hi (ab_addr bt) (ab_size bt)) INbt ltac:(lia) ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia)
                ltac:(unfold oshw_hi, A_SB, amem in *; aceil; clear -CEILB TC T0; Z.div_mod_to_equations; lia)) as POT.
  pose proof (aypol_block Y _ _ _ _ LINK bt (ab_addr bt) (ab_addr bt + ab_size bt) INbt ltac:(lia) ltac:(lia) T0 ltac:(aceil; lia)) as PT.
  pose proof (aypol_img Y _ _ _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  eapply evtA_cut.
  { eapply (seg_u1 HEX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w0 w96 sur cpw F1 fc1 m1 SQ FF B S n e lo cp (ab_addr bt) (ab_size bt) str);
      [ exact MI1 | exact STA1 | exact FRQ | exact ST1 | exact CEIL | lia | lia | exact SQ32 | exact SB0
      | exact TXT1 | exact SF | exact NL | exact OSBT | exact T1 | exact T2 | exact OH | exact TC
      | lia | exact E5 | exact N26 | pose proof (proj1 TXT1); lia | exact S47
      | exact HHEX | exact HX | lia
      | exact PSTKL | exact PSSH | exact POT | exact PT | exact PIMG ]. }
  cbv beta. intros ms2 (rax & x1 & x2 & x3 & x4 & x5 & x6 & x7 & q0 & q1 & q2 & q3 & q4 & q5 & q6 & m2 & pc' & -> & CASES & MU2 & WM2 & MI2 & ST2 & STA2 & FRQ2 & SB2 & TXT2 & OSBT2).
  clear FRQ.
  destruct CASES as [[HNS ->]| [HS ->]].
  - (* [comment removed for export] *)
    apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHKb R2]. clear LINK BACK PSTKL PSSH POT PT PIMG.
  destruct (own_writes _ _ _ _ _ _ AHKb MU2 WM2 ltac:(repeat (constructor; [split; [cbn; lia| cbn [fst snd]; lia]|]); constructor)) as (AHK2 & PRES12 & YSf).
  pose proof (YSf YS1) as YS2. clear YSf AHKb.
  unfold dsaved in SV1. trw SV1 MU2 WM2. trw FFA MU2 WM2. trw U5 MU2 WM2. trw FJ MU2 WM2. trw FFP MU2 WM2. unfold fsh_in in FSH. trw FSH MU2 WM2. fold fsh_in in FSH. fold dsaved in SV1.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES12 YAF1 ltac:(destruct AFIN as (ba & Hba & A1 & A2 & _); exists ba; split; [apply INR; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB A1 A2; Z.div_mod_to_equations; lia)) as YAF2.
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
  destruct (buf_keep _ _ _ _ _ _ _ _ AHK2 PRES12 BR1 OSD1) as (BR2 & OSB2 & OSD2).
  assert (PRES2 : ay_pres REST LF (bv_unsigned sp) [] m _) by (eapply ay_pres_trans; [exact PRES1|]; eapply (ay_pres_weaken Y); [exact PRES12| lia| exact INR| intros f Hf; exact Hf| auto]).
    eapply (dec_cp f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m2 mo2 s1' b1 mb1 LK e cp w0 w96 sur (Z_to_bv 64 cp) ubs); try eassumption; try lia.
    + eapply RRT; [exact R1| exact R2].
    + intros r Hr. apply HL. eapply (dlf_u f' b0 str n beg e cp b1 r); [lia| exact CB| exact CU| replace (e + 1 + 1) with (e + 2) by lia; exact HX| exact HNS| exact HLB1|].
      replace (e + 1 + 1 + 3 + 1) with (e + 6) by lia. unfold RY_decode1.u8enc in Hr. exact Hr.
  - (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (seg_u2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m2 SQ FF B S n e cp (ab_addr bt) (ab_size bt) str);
        [ exact MI2 | exact TXT2 | exact SF | exact NL | exact OSBT2 | exact T1 | exact T2 | exact OH | exact TC
        | lia | exact E5 | exact N26 | pose proof (proj1 TXT1); lia | exact S47 | lia
        | exact POT | exact PT | exact PIMG ]. }
    cbv beta. intros ms3 (y0 & y1 & y2 & y3 & [[DL ->]| [DL ->]]). all: unfold DST.
    + (* [comment removed for export] *)
      apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHKb R2]. clear LINK BACK PSTKL PSSH POT PT PIMG.
  destruct (own_writes _ _ _ _ _ _ AHKb MU2 WM2 ltac:(repeat (constructor; [split; [cbn; lia| cbn [fst snd]; lia]|]); constructor)) as (AHK2 & PRES12 & YSf).
  pose proof (YSf YS1) as YS2. clear YSf AHKb.
  unfold dsaved in SV1. trw SV1 MU2 WM2. trw FFA MU2 WM2. trw U5 MU2 WM2. trw FJ MU2 WM2. trw FFP MU2 WM2. unfold fsh_in in FSH. trw FSH MU2 WM2. fold fsh_in in FSH. fold dsaved in SV1.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES12 YAF1 ltac:(destruct AFIN as (ba & Hba & A1 & A2 & _); exists ba; split; [apply INR; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB A1 A2; Z.div_mod_to_equations; lia)) as YAF2.
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
  destruct (buf_keep _ _ _ _ _ _ _ _ AHK2 PRES12 BR1 OSD1) as (BR2 & OSB2 & OSD2).
  assert (PRES2 : ay_pres REST LF (bv_unsigned sp) [] m _) by (eapply ay_pres_trans; [exact PRES1|]; eapply (ay_pres_weaken Y); [exact PRES12| lia| exact INR| intros f Hf; exact Hf| auto]).
      unfold ADP_TAIL0.
      change A_LIT_Q with LIT0.
      eapply (dec_tail f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m2 mo2 s1' b1 mb1 LK (e + 5) e LIT0 [63] [0; 0; 0; 0; 0; 0] w0 w96 sur (Z_to_bv 64 cp) ubs); try eassumption; try lia.
      * eapply RRT; [exact R1| exact R2].
      * replace LIT0 with (LIT0 + 32 * 0) by lia. apply (lit_bytes m2 0 MI2). lia.
      * repeat (constructor; [cbn; lia|]). constructor.
      * intros [X|[]]. lia.
      * cbn. lia.
      * unfold zlength, LIT0. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. clear. Z.div_mod_to_equations. lia.
      * unfold zlength. cbn [length]. lia.
      * left. exists 0. split; [lia|]. split; [unfold LIT0; lia| reflexivity].
      * unfold zlength. cbn [length]. lia.
      * replace (e + 5 + 1) with (e + 6) by lia. exact HREST.
      * intros r Hr. apply HL. eapply (dlf_uq f' b0 str n beg e cp b1 r); [lia| exact CB| exact CU| replace (e + 1 + 1) with (e + 2) by lia; exact HX| exact HS| | exact HLB1|].
        -- replace (e + 1 + 1 + 3 + 2) with (e + 7) by lia. replace (e + 1 + 1 + 3 + 1) with (e + 6) by lia. unfold c_bslash, c_u. unfold dlook in DL. exact DL.
        -- replace (e + 1 + 1 + 3 + 1) with (e + 5 + 1) by lia. exact Hr.
    + (* [comment removed for export] *)
      unfold dlook in DL. apply andb_prop in DL. destruct DL as [DL CU2]. apply andb_prop in DL. destruct DL as [E7 CB2].
      apply Z.ltb_lt in E7. apply Z.eqb_eq in CB2. apply Z.eqb_eq in CU2.
      assert (LX2 : e + 11 < n /\ (forall k, 0 <= k < 4 -> is_vhc (znth str (e + 8 + k)) = true) /\ sbody_ix str (e + 12) n).
      { inversion HREST as [| i j Hlt Hnb Hrest| i j Hlt Hb Hvec Hrest| i j Hlt Hb Hu Hhex Hrest]; subst; [lia| unfold c_bslash in *; congruence| |].
        - exfalso. replace (e + 6 + 1) with (e + 7) in Hvec by lia. rewrite CU2 in Hvec. revert Hvec. clear. vm_compute. discriminate.
        - split; [lia|]. split; [intros k Hk; replace (e + 8 + k) with (e + 6 + 2 + k) by lia; apply Hhex; lia| replace (e + 12) with (e + 6 + 6) by lia; exact Hrest]. }
      destruct LX2 as (E11 & HHEX2 & HREST2).
      destruct (yhexToDigit_bound str (e + 8) HHEX2) as (sr & HX2 & SURR).
      eapply evtA_cut.
      { eapply (seg_u3 HEX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w0 w96 sur F1 fc1 m2 SQ FF B S n e lo cp sr (ab_addr bt) (ab_size bt) str);
          [ exact MI2 | exact STA2 | exact FRQ2 | exact ST2 | exact CEIL | lia | lia | exact SQ32 | exact SB2
          | exact TXT2 | exact SF | exact NL | exact OSBT2 | exact T1 | exact T2 | exact OH | exact TC
          | lia | exact E11 | exact N26 | pose proof (proj1 TXT1); lia | exact S47 | lia
          | exact HHEX2 | exact HX2 | lia
          | exact PSTKL | exact PSSH | exact POT | exact PT | exact PIMG ]. }
      cbv beta. intros ms4 (rax' & z1 & z2 & z3 & z4 & z5 & z6 & z7 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & m3 & -> & CSR & MU3 & WM3 & MI3 & ST3 & STA3 & FRQ3 & SB3 & TXT3 & OSBT3).
      apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHKb R2]. clear LINK BACK PSTKL PSSH POT PT PIMG.
      pose proof (munch_trans _ _ _ _ MU2 MU3) as MU23. pose proof (wmono_trans _ _ _ _ WM2 WM3) as WM23. clear MU2 WM2 MU3 WM3 MI2 ST2 STA2 FRQ2 SB2 TXT2 OSBT2.
  destruct (own_writes _ _ _ _ _ _ AHKb MU23 WM23 ltac:(repeat (constructor; [split; [cbn; lia| cbn [fst snd]; lia]|]); constructor)) as (AHK2 & PRES12 & YSf).
  pose proof (YSf YS1) as YS2. clear YSf AHKb.
  unfold dsaved in SV1. trw SV1 MU23 WM23. trw FFA MU23 WM23. trw U5 MU23 WM23. trw FJ MU23 WM23. trw FFP MU23 WM23. unfold fsh_in in FSH. trw FSH MU23 WM23. fold fsh_in in FSH. fold dsaved in SV1.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES12 YAF1 ltac:(destruct AFIN as (ba & Hba & A1 & A2 & _); exists ba; split; [apply INR; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB A1 A2; Z.div_mod_to_equations; lia)) as YAF2.
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU23| exact WM23| cbv [disjoint_from fst snd]; lia].
  destruct (buf_keep _ _ _ _ _ _ _ _ AHK2 PRES12 BR1 OSD1) as (BR2 & OSB2 & OSD2).
  assert (PRES2 : ay_pres REST LF (bv_unsigned sp) [] m _) by (eapply ay_pres_trans; [exact PRES1|]; eapply (ay_pres_weaken Y); [exact PRES12| lia| exact INR| intros f Hf; exact Hf| auto]).
      eapply (dec_4 f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m3 mo2 s1' b1 mb1 LK e (combine_surrogate cp sr) w0 w96 (Z_to_bv 64 sr) (Z_to_bv 64 (combine_surrogate cp sr)) ubs); try eassumption; try lia.
      * eapply RRT; [exact R1| exact R2].
      * intros r Hr. apply HL.
        eapply (dlf_us f' b0 str n beg e cp sr b1 r);
          [ lia | exact CB | exact CU | replace (e + 1 + 1) with (e + 2) by lia; exact HX | exact HS | lia
          | replace (e + 1 + 1 + 3 + 1) with (e + 6) by lia; unfold c_bslash; exact CB2 | replace (e + 1 + 1 + 3 + 2) with (e + 7) by lia; unfold c_u; exact CU2
          | replace (e + 1 + 1 + 3 + 1 + 2) with (e + 8) by lia; exact HX2 | exact HLB1 | ].
        replace (e + 1 + 1 + 3 + 1 + 5 + 1) with (e + 12) by lia. unfold RY_decode1.u8enc in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma esc_lit_k : forall c u, simple_escape c = Some u ->
  exists k, 1 <= k < 9 /\ esc_lit c = LIT0 + 32 * k /\ litc k = u /\ In c [34; 47; 92; 98; 102; 110; 114; 116; 117].
Proof. aceil.
  intros c u H. unfold simple_escape, c_r, c_n, c_bslash, c_slash, c_quote, c_f, c_b, c_t in H.
  Ltac esck k := exists k; split; [lia|]; split; [reflexivity|]; split; [reflexivity|]; cbn [In]; lia.
  destruct (Z.eqb_spec c 114) as [->|N1]; [injection H as <-; esck 1|].
  destruct (Z.eqb_spec c 110) as [->|N2]; [injection H as <-; esck 2|].
  destruct (Z.eqb_spec c 92) as [->|N3]; [injection H as <-; esck 3|].
  destruct (Z.eqb_spec c 47) as [->|N4]; [injection H as <-; esck 4|].
  destruct (Z.eqb_spec c 34) as [->|N5]; [injection H as <-; esck 5|].
  destruct (Z.eqb_spec c 102) as [->|N6]; [injection H as <-; esck 6|].
  destruct (Z.eqb_spec c 98) as [->|N7]; [injection H as <-; esck 7|].
  destruct (Z.eqb_spec c 116) as [->|N8]; [injection H as <-; esck 8|].
  discriminate.
Qed.

Lemma litc_range : forall k, 0 <= litc k < 256.
Proof. aceil.
  intros k. unfold litc. generalize (Z.to_nat k) as i. intros i.
  do 9 (destruct i as [|i]; [cbn; lia|]). destruct i; cbn; lia.
Qed.

Lemma litc_nz : forall k, 0 <= k < 9 -> litc k <> 0.
Proof. aceil.
  intros k Hk. destruct (lit_cases k Hk) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; cbv; lia.
Qed.

Lemma dec_step : forall f', head_ok f' -> head_ok (Datatypes.S f').
Proof. aceil.
  intros f' HEAD. red. intros until j37.
  intros AHK1 YS1 MI1 ST1 GAP1 FRM1 FRQ SV1 FFA U5 FJ FFP FSH TXT1 YAF1 BR1 BI MBS OSB1 OSD1 PRES1 R1 SO1 CRED1 RR0 LKc ELK UB HBE HEN SBX HF HL.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof CEIL' as CE. pose proof LO' as LOx. pose proof (zlength_nonneg str) as NL0.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof FFce as FC. aceil.
  assert (E8F : FF = 8 * (FF / 8)) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  assert (EB : mb_addr mb = B) by (unfold B; exact MBS).
  assert (LU5 : length ubs = 5%nat) by exact (proj1 (proj1 (proj1 U5))).
  assert (INR : forall b2, In b2 REST -> In b2 (abl (buf_blocks mb b) ++ LK ++ REST)) by (intros b2 Hb2; apply in_or_app; right; apply in_or_app; right; exact Hb2).
  destruct (txt_obj _ _ _ _ _ AHK1 INR ltac:(lia)) as (bt & INbt & OSBT & T1 & T2 & OH & TC & T0 & T8).
  pose proof OSBT as (OT8 & OTn0 & TSH).
  pose proof (dstr_byte str e SF) as CR.
  (* [comment removed for export] *)
  arz_seg KIPY AHK1.
  pose proof (aypol_bshadow Y _ _ _ _ LINK bt (oshw_lo (ab_addr bt)) (oshw_hi (ab_addr bt) (ab_size bt)) INbt ltac:(lia) ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia)
                ltac:(unfold oshw_hi, A_SB, amem in *; aceil; clear -CEILB TC T0; Z.div_mod_to_equations; lia)) as POT.
  pose proof (aypol_block Y _ _ _ _ LINK bt (ab_addr bt) (ab_addr bt + ab_size bt) INbt ltac:(lia) ltac:(lia) T0 ltac:(aceil; lia)) as PT.
  pose proof (aypol_ffshadow Y _ ((0, FF) :: LF) _ _ LINK (0, FF) (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) as PFFS.
  eapply evtA_cut.
  { eapply (seg_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 SQ FF B S n e beg (znth str e) (ab_addr bt) (ab_size bt) (blk_shadow (ab_size bt)));
      [ exact MI1 | exact (dstr_read m1 S str e TXT1 ltac:(lia)) | exact CR
      | exact TSH | reflexivity | exact T8 | exact T0 | lia | lia | aceil; exact TC
      | exact FSH | exact FFsh | exact FC | exact FFal | exact HBE | exact HEN | exact N26 | pose proof (proj1 TXT1); lia | exact S47
      | exact POT | exact PT | exact PFFS ]. }
  cbv beta. intros ms2 (x0 & x1 & x2 & m2 & MI2 & CASES).
  destruct CASES as [(NB & LT & -> & ->)| [(NB & EQ & -> & ->)| (CBk & MU2 & WM2 & FSH2 & ->)]]. all: unfold DST.
  - (* [comment removed for export] *)
    apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHK2 R2]. clear LINK BACK POT PT PFFS.
    assert (NB' : znth str e <> c_bslash) by (unfold c_bslash; exact NB).
    assert (SB1 : sbody_ix str (e + 1) n) by (inversion SBX; subst; [lia| assumption| congruence| congruence]).
    eapply (HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 mo2 s1' b mb LK beg (e + 1) w0 w96 sur cp ubs wf0 wf8 wf16 j24 j37);
      [ exact AHK2 | exact YS1 | exact MI1 | exact ST1 | exact GAP1 | exact FRM1
      | exact FRQ | exact SV1 | exact FFA | exact U5 | exact FJ | exact FFP | exact FSH | exact TXT1
      | exact YAF1 | exact BR1 | exact BI | exact MBS | exact OSB1 | exact OSD1
      | exact PRES1 | eapply RRT; [exact R1| exact R2] | exact SO1 | exact CRED1 | exact RR0
      | exact LKc | exact ELK | exact UB | lia | lia | exact SB1 | lia
      | intros r Hr; apply HL; apply dlf_plain; [lia| exact NB'| exact Hr] ].
  - (* [comment removed for export] *)
    apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHK2 R2]. clear LINK BACK POT PT PFFS.
    assert (NB' : znth str e <> c_bslash) by (unfold c_bslash; exact NB).
    pose proof (sub_chunk m1 _ [] [C8 wf0] [C8 wf8; C8 wf16; CB 8 j24] ltac:(exact FFA)) as FF04. cbn [cells_size csize Nat.add Z.of_nat app] in FF04. rewrite Z.add_0_r in FF04.
    pose proof (sub_chunk m1 _ [C8 w0; C8 (Z_to_bv 64 1047552); C8 (Z_to_bv 64 (FF + 32)); C8 (Z_to_bv 64 55296); C8 (Z_to_bv 64 64512);
                                 C8 (Z_to_bv 64 A_LIT_BS); C8 (Z_to_bv 64 A_LIT_BSL); C8 (Z_to_bv 64 A_LIT_SL); C8 (Z_to_bv 64 A_LIT_QT); C8 (Z_to_bv 64 A_LIT_CR)]
                   [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] [C8 w96; C8 (Z_to_bv 64 FF); C4 sur; C4 cp] ltac:(exact FRQ)) as L112. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in L112.
    unfold fsh_out, F1b, F3b, F8b in FSH.
    eapply (dec_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 mo2 s1' b mb LK beg (e + 1));
      [ exact AHK2 | exact YS1 | exact MI1 | exact ST1 | exact GAP1 | exact FRM1
      | exact FRQ | reflexivity | exact L112 | exact SV1 | exact FF04 | exact FFP | exact FSH | exact TXT1
      | exact YAF1 | exact BR1 | exact BI | exact MBS | exact OSB1 | exact OSD1
      | exact PRES1 | eapply RRT; [exact R1| exact R2] | exact SO1 | exact CRED1 | exact RR0
      | exact LKc | exact ELK | exact UB | lia | lia
      | intros bf Hbf; eapply exit_leaf; [| exact Hbf]; apply HL; apply dlf_plain; [lia| exact NB'|];
        destruct f' as [|f'']; [exfalso; lia|]; apply dlf_exit; lia ].
  - (* [comment removed for export] *)
    assert (CB : znth str e = c_bslash) by (unfold c_bslash; exact CBk).
    assert (E1 : e + 1 < n) by (inversion SBX; subst; [lia| congruence| lia| lia]).
    (* [comment removed for export] *)
    assert (ESC : (exists u k, simple_escape (znth str (e + 1)) = Some u /\ 1 <= k < 9 /\ esc_lit (znth str (e + 1)) = LIT0 + 32 * k /\ litc k = u /\ sbody_ix str (e + 2) n)
                  \/ (znth str (e + 1) = 117 /\ e + 5 < n /\ (forall q, 0 <= q < 4 -> is_vhc (znth str (e + 2 + q)) = true) /\ sbody_ix str (e + 6) n)).
    { inversion SBX as [| i j Hlt Hnb Hrest| i j Hlt Hb Hvec Hrest| i j Hlt Hb Hu Hhex Hrest]; subst; [lia| congruence| |].
      - left. pose proof (vec_simple_escape _ Hvec) as HSE. destruct (simple_escape (znth str (e + 1))) as [u|] eqn:HU; [| congruence].
        destruct (esc_lit_k _ _ HU) as (k & Hk & EL & LC & _). exists u, k. split; [reflexivity|]. split; [exact Hk|]. split; [exact EL|]. split; [exact LC| exact Hrest].
      - right. unfold c_u in Hu. split; [exact Hu|]. split; [exact Hlt|]. split; [exact Hhex| exact Hrest]. }
    assert (INc2 : In (znth str (e + 1)) [34; 47; 92; 98; 102; 110; 114; 116; 117]).
    { destruct ESC as [(u & k & HU & _)| (Hu & _)]; [destruct (esc_lit_k _ _ HU) as (k' & _ & _ & _ & X); exact X| rewrite Hu; cbn [In]; lia]. }
    apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHKb R2]. clear LINK BACK POT PT PFFS.
    destruct (own_writes _ _ _ _ _ _ AHKb MU2 WM2 ltac:(constructor; [split; [cbn [fst snd]; lia| cbn [fst snd]; lia]| constructor])) as (AHK2 & PRES12 & YSf).
    pose proof (YSf YS1) as YS2. clear YSf AHKb.
    unfold dspill in FRQ. unfold dsaved in SV1.
    trw FRQ MU2 WM2. trw SV1 MU2 WM2. trw FFA MU2 WM2. trw U5 MU2 WM2. trw FJ MU2 WM2. trw FFP MU2 WM2.
    pose proof (aypres_block _ _ _ _ _ _ _ PRES12 YAF1 ltac:(destruct AFIN as (ba & Hba & A1 & A2 & _); exists ba; split; [apply INR; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB A1 A2; Z.div_mod_to_equations; lia)) as YAF2.
    eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
    eapply (stk_transport_disjoint bsegs) in ST1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
    destruct (buf_keep _ _ _ _ _ _ _ _ AHK2 PRES12 BR1 OSD1) as (BR2 & OSB2 & OSD2).
    pose proof (txt_pres _ _ _ _ _ PRES12 INR TXT1) as TXT2.
    assert (PRES2 : ay_pres REST LF (bv_unsigned sp) [] m m2) by (eapply ay_pres_trans; [exact PRES1|]; eapply (ay_pres_weaken Y); [exact PRES12| lia| exact INR| intros f Hf; exact Hf| auto]).
    clear MI1 TXT1 YAF1 BR1 OSB1 OSD1 AHK1 YS1 FSH PRES1 PRES12.
    (* [comment removed for export] *)
    assert (SRCL : zlength (zslice str beg (e - beg)) = e - beg) by (apply zslice_length; lia).
    pose proof (sub_chunk m2 _ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV1)) as SV16.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV16 by lia.
    eapply (BAPP2 ((0, FF) :: LF) (LK ++ REST) mb b AF (S + beg) (zslice str beg (e - beg)) lo RR K);
      [ ba_app EB ltac:(pose proof (proj1 TXT2); lia)
      | exact K0
      | apply AYST_split; split; [exact AHK2| exact YS2]
      | exact BR2 | exact BI | exact YAF2
      | eapply yaf_ok_now; [exact AHK2| exact INR| intros b0 Hb0; apply in_or_app; right; exact Hb0]
      | exact OSB2
      | intros Hd; exact (proj1 (OSD2 Hd))
      | apply abytes_at_zslice; [exact TXT2| lia]
      | apply dForall_zslice; exact SF
      | intros _; pose proof (proj1 TXT2); lia
      | rewrite SRCL; lia
      | rewrite SRCL; lia
      | (* [comment removed for export] *) unfold ysrc_range; rewrite SRCL;
        destruct (Z.lt_ge_cases 0 (e - beg)) as [Hn|Hn]; [| right; right; right; clear -CEILB Hn HBE; lia];
        destruct TR as [(bt' & HBT & U1 & U2)|N0']; [| exfalso; lia];
        left; exists bt'; split; [apply in_or_app; right; exact HBT| lia]
      | (* [comment removed for export] *)
        unfold ysrc_win; rewrite SRCL, USQ; intros Hn s' LBx m' mo' AHK' PRES';
        destruct TR as [(bt' & HBT & U1 & U2)|N0']; [| exfalso; lia];
        assert (INx : In bt' (LBx ++ LK ++ REST)) by (apply in_or_app; right; apply in_or_app; right; exact HBT);
        destruct (ICPB _ _ _ _ _ bt' (S + beg) (e - beg) AHK' INx ltac:(lia) ltac:(lia) ltac:(lia)) as (ws & SW & RC & SH1' & SH2');
        exists ws; split; [exact SW|]; split; [exact RC|];
        eapply aypol_pages;
        [ eapply ICPR; [exact AHK'| exact INx| lia| lia| lia]
        | pose proof (shw_geom A_SB (S + beg) (e - beg) ltac:(unfold A_SB; lia) ltac:(pose proof (proj1 TXT2); lia) ltac:(lia)) as G; cbv zeta in G; unfold A_SB in *; clear -CEILB G; lia
        | clear -CEILB SH1'; unfold A_SB in *; lia ]
      | unfold ayframe_pre, AY_BUF_APPEND_STACK, AMALLOC_STACK; aceil; rewrite USQ;
        split; [exact ST1|]; split; [lia|]; split; [unfold AY_DECODE_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK in LO; lia|]; split; [lia|];
        split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|]; split; [exact MI2|]; split; [exact TP| exact FRM1]
      | rewrite EB; reflexivity | reflexivity | rewrite SRCL; reflexivity
      | exact CRED1 | exact RR0
      | rewrite nbig_app2; pose proof (nbig_le_len2 LK); destruct LK; [cbn in *; lia| destruct (LKc ltac:(discriminate)) as [_ L1]; cbn [length] in *; lia]
      | rewrite USQ; eapply USTEP; [unfold ADP_RET2; rewrite unsigned_lit by lia; exact URA_a1| lia| exact SV16
        | eapply UFRAME; [| exact UA]; intros a Ha; destruct (PRES2 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]; exact E]
      | ].
    cbv beta. intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c F3 fc3 m3 mo3 s3' b' mb' LK0 POST.
    destruct POST as (SO3 & R3 & CRED3 & (MI3 & ST3 & FRM3 & _ & PRES3) & YAF3 & YLA & BR3 & MBS3 & OS3 & OSD3 & LKZ3 & AY3 & LKB3 & NLK).
    rewrite USQ in ST3, PRES3.
    replace (ret_pc (Z_to_bv 64 ADP_RET2)) with (Z_to_bv 64 ADP_RET2) by (symmetry; apply ret_pc_even; [unfold ADP_RET2; lia| reflexivity]).
    apply AYST_split in AY3. destruct AY3 as [AHK3 YS3].
    pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 SV1 ltac:(lia)) as SV3. clear SV1 SV16.
    pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 FRQ ltac:(lia)) as FRQ3. clear FRQ.
    assert (GAP3 : stk bsegs m3 (SQ + 120) (bv_unsigned sp + -104)).
    { eapply stk_agree; [eapply ay_pres_agree; exact PRES3| exact GAP1| intros a Ha; split; [left; lia| intros F0; exact F0]]. }
    clear GAP1.
    Ltac trf3 H PRES3 FF := first
      [ pose proof (aypres_fframe _ _ _ _ _ _ _ (0, FF) PRES3 H (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_0; lia))
      | pose proof (aypres_fframe _ _ _ _ _ _ _ (0, FF) PRES3 H (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) ].
    trf3 FFA PRES3 FF. trf3 U5 PRES3 FF. trf3 FJ PRES3 FF. trf3 FFP PRES3 FF. unfold fsh_in in FSH2. trf3 FSH2 PRES3 FF.
    clear FFA U5 FJ FFP FSH2. rename H into FFA3. rename H0 into U53. rename H1 into FJ3. rename H2 into FFP3. rename H3 into FSH3.
    pose proof (txt_pres _ _ _ _ _ PRES3 ltac:(intros b0 Hb0; apply in_or_app; right; exact Hb0) TXT2) as TXT3.
    assert (PRES3w : ay_pres REST LF (bv_unsigned sp) [] m m3).
    { eapply ay_pres_trans; [exact PRES2|]. eapply (ay_pres_weaken Y); [exact PRES3| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0| intros f Hf; right; exact Hf| auto]. }
    assert (INR3 : forall b0, In b0 REST -> In b0 (abl (buf_blocks mb' b') ++ LK0 ++ LK ++ REST)).
    { intros b0 Hb0. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hb0. }
    pose proof (ypost_yleaf _ _ _ (ybuf_append_post2 b _ BI ltac:(rewrite SRCL; lia)) YLA) as AP. cbv beta in AP. destruct AP as (BI' & APok & APerr).
    assert (UB' : yb_used b' <= e).
    { destruct (yb_state b') eqn:EST; [destruct (APok eq_refl) as (_ & -> & _); rewrite SRCL; lia| destruct (APerr ltac:(discriminate)) as [-> _]; lia| destruct (APerr ltac:(discriminate)) as [-> _]; lia]. }
    assert (LKc3 : LK0 ++ LK <> [] -> yb_state b' <> BS_ok /\ length (LK0 ++ LK) = 1%nat).
    { intros NE. destruct LK0 as [|k0 LK0'].
      - cbn [app] in *. destruct (LKc NE) as [SB L1]. split; [| exact L1]. intros OK'. apply SB. exact (proj1 (APok OK')).
      - destruct (LKB3 ltac:(discriminate)) as [SB' L1]. specialize (NLK ltac:(discriminate)).
        destruct LK as [|k LK']; [rewrite app_nil_r; split; [exact SB'| exact L1]|].
        exfalso. destruct (LKc ltac:(discriminate)) as [SB _]. exact (SB NLK). }
    assert (MBS3' : mb_same mbd mb') by (unfold mb_same in *; congruence).
    clear PRES3 MI2 TXT2 BR2 OSB2 OSD2 AHK2 YS2 LKB3 NLK MU2 WM2.
    (* [comment removed for export] *)
    destruct (txt_obj _ _ _ _ _ AHK3 INR3 ltac:(lia)) as (bt3 & INbt3 & OSBT3 & V1 & V2 & OH3 & TC3 & T03 & T83).
    pose proof OSBT3 as (OT83 & OTn03 & TSH3).
    arz_seg KIPY AHK3.
    pose proof (aypol_bshadow Y _ _ _ _ LINK bt3 (oshw_lo (ab_addr bt3)) (oshw_hi (ab_addr bt3) (ab_size bt3)) INbt3 ltac:(lia) ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia)
                  ltac:(unfold oshw_hi, A_SB, amem in *; aceil; clear -CEILB TC3 T03; Z.div_mod_to_equations; lia)) as POT.
    pose proof (aypol_block Y _ _ _ _ LINK bt3 (ab_addr bt3) (ab_addr bt3 + ab_size bt3) INbt3 ltac:(lia) ltac:(lia) T03 ltac:(aceil; lia)) as PT.
    pose proof (aypol_stack Y _ ((0, FF) :: LF) _ _ LINK SQ (SQ + 120) ltac:(aceil; lia) ltac:(lia)) as PSTK.
    pose proof (aypol_img Y _ _ _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
    eapply evtA_cut.
    { eapply (seg_esc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w0 w96 sur cp F3 fc3 m3 SQ FF B S n e beg (znth str (e + 1)) (ab_addr bt3) (ab_size bt3) (blk_shadow (ab_size bt3)));
        [ exact MI3 | exact FRQ3 | aceil; lia | lia
        | exact (dstr_read m3 S str (e + 1) TXT3 ltac:(lia)) | exact INc2
        | exact TSH3 | reflexivity | exact T83 | exact T03 | lia | lia | aceil; exact TC3
        | lia | exact E1 | exact N26 | pose proof (proj1 TXT3); lia | exact S47
        | exact PSTK | exact POT | exact PT | exact PIMG ]. }
    cbv beta. intros ms4 (x0' & x1' & x2' & CASES).
    apply evtA_done. intros mo4 Hag4 HLI4 Hh4. destruct (BACK mo4 Hag4 HLI4) as [AHK4 R4]. clear LINK BACK PSTK POT PT PIMG.
    destruct CASES as [[NU ->]| [EU ->]]. all: unfold DST.
    + (* [comment removed for export] *)
      destruct ESC as [(u & k & HU & Hk & EL & LC & Hrest)| (Hu & _)]; [| exfalso; exact (NU Hu)].
      rewrite EL. subst u.
      eapply (dec_tail f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 mo4 s3' b' mb' (LK0 ++ LK) (e + 1) e (LIT0 + 32 * k) [litc k] [0; 0; 0; 0; 0; 0] w0 w96 sur cp ubs wf0 wf8 wf16 j24 j37);
        [ rewrite <- app_assoc; exact AHK4 | exact YS3 | exact MI3 | exact ST3 | exact GAP3 | exact FRM3
        | exact FRQ3 | exact SV3 | exact FFA3 | exact U53 | exact FJ3 | exact FFP3 | exact FSH3 | exact TXT3
        | exact YAF3 | exact BR3 | exact BI' | exact MBS3' | exact OS3 | exact OSD3
        | exact PRES3w | eapply RRT; [exact R1|]; eapply RRT; [exact R2|]; eapply RRT; [exact R3| exact R4] | rewrite SO3; exact SO1 | exact CRED3 | exact RR0
        | exact LKc3 | lk0
        | apply (lit_bytes m3 k MI3); lia
        | apply Forall_cons; [apply litc_range|]; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil
        | intros [X|[]]; exact (litc_nz k ltac:(lia) X)
        | cbn; lia
        | unfold zlength, LIT0; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB Hk; Z.div_mod_to_equations; lia
        | unfold zlength; cbn [length]; lia
        | left; exists k; split; [lia|]; split; [reflexivity| reflexivity]
        | unfold zlength; cbn [length]; lia
        | lia | lia
        | replace (e + 1 + 1) with (e + 2) by lia; exact Hrest
        | lia | lia
        | intros r Hr; apply HL; eapply (dlf_esc f' b str n beg e (litc k) b' r); [lia| exact CB| exact HU| exact YLA| exact Hr] ].
    + (* [comment removed for export] *)
      destruct ESC as [(u & k & HU & _)| (Hu & E5 & Hhex & Hrest)]; [exfalso; rewrite EU in HU; cbv in HU; discriminate|].
      eapply (dec_uesc f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 mo4 s3' b b' mb' (LK0 ++ LK) beg e w0 w96 sur cp ubs wf0 wf8 wf16 j24 j37);
        [ rewrite <- app_assoc; exact AHK4 | exact YS3 | exact MI3 | exact ST3 | exact GAP3 | exact FRM3
        | exact FRQ3 | exact SV3 | exact FFA3 | exact U53 | exact LU5 | exact FJ3 | exact FFP3 | exact FSH3 | exact TXT3
        | exact YAF3 | exact BR3 | exact BI' | exact MBS3' | exact OS3 | exact OSD3
        | exact PRES3w | eapply RRT; [exact R1|]; eapply RRT; [exact R2|]; eapply RRT; [exact R3| exact R4] | rewrite SO3; exact SO1 | exact CRED3 | exact RR0
        | exact LKc3 | lk0 | exact HBE | exact E5 | exact CBk | exact EU | exact Hhex | exact Hrest | exact HF | exact UB' | exact YLA | exact HL ].
Qed.
End Fn.
End W.
End RC__1.
