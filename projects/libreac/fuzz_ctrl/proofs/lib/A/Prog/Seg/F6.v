(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 2560 of its 2603 lines of code are new or changed and 353 lines of the source are left out. *)
(* Segment F6 (0x81ec0-0x81f60 plus the out-of-line stubs 0x82a38-0x82a40, 0x82ab0-0x82ab8, 0x82c90, 0x82cfc,
   0x82d2c; plan-asan 2 row F6, call PARSE@0x81f60): the 32-byte record sum of the long frame and the second
   reac_ctrl_parse call, stated with the official cuts of SlotInv.v (no local cut text).
     0x81ec0-0x81ee4  the byte-sum loop over [s7+18, s7+50): per byte the instrumented check (a load of the shadow
                      byte at (a >> 3) + s10 and a compare; slow path 0x81eec-0x81ef4, error path 0x82c90 shown
                      NOT reached), then a1 += byte; a3 counts 32 down
     0x81ef8-0x81f34  the checks of the bytes s7+16 (slow path 0x82a38 -> 0x82cfc) and s7+17 (slow path
                      0x82ab0 -> 0x82d2c), both shown NOT reached; s9 = (byte16 = 0 and byte17 = 0) = b2z (t_tfill j)
     0x81f38-0x81f40  snez a0,s8 ; ld a2,240(s1) ; bne a0,a2,abort: [s1+240] = b2z (t_8819 j) = (s8 <> 0), not taken
     0x81f44-0x81f50  [s1+280] = (low byte of the sum = 0) = b2z (t_sum_ok j) ; s4 = its negation
     0x81f54-0x81f60  mv a0,s7 ; mv a1,s2 ; li a2,0 ; jal reac_ctrl_parse
   Lemmas: seg_F6_e28 (0x81ec0 -> 0x81f54, exit SlotInv.Inv_A81f54_at), seg_F6_ebc (0x81f54 -> 0x81f64, exit
   SlotInv.Inv_A81f64_at) and seg_F6 (both).

   The call runs through the lib/A contract reac_ctrl_parse_contract (a Section Hypothesis), with f = phi,
   n = flen g j and o = 0 (no output cell). The contract needs mem_inv, which no cut carries: the call runs on
   MemNorm.normalize of the memory and comes back with MemNorm.evt_normalize (every premise and post fact of the
   contract is a bytes_at / stk / addressable / shadow_rw / fp fact, which crosses mem_rel above the image). The
   callee's side-stack bundle (`fp [1%nat] ...` and `reac_ctrl_parse_tls`) is built at the call from FRA's
   AsanRTInv.RT (RT_fs_cells and friends), the allocator laws and SlotInv.b5_FS (f6_fp_call, the reac_ctrl_parse
   form of F9's f9_fp_call). The call writes its window, the class-1 side-stack ranges and their shadow and the
   shadow of its window (f6_PW): FRA moves across that write by f6_fra_call (RT by RT_meta_write, AH / stklo by
   a_laws_fs_store, the rest by f6_run, the shadow-writing form of Tac_slot.sl_fr_cl), ENT by ent_munch and
   ent_mat. The word u32 (fr + 176) of b5_K is carried: the call writes no frame byte. f6_keep moves the cut
   skeleton (HB, FLSI, LK, b5_C) across both segments' writes. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib RcModel RcLib RcParse RcAsanLib RcLay
  RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c memcmp_c bcmp_wrap_c
  asan_stack_malloc_c RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---------------- model and layout facts ---------------- *)

(* The 50-byte record of the model has 50 bytes. *)
Lemma f6_tg_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

(* reac_ctrl_parse reads only bytes below 50, and none of a record below 50 bytes. *)
Lemma f6_cp_rd_lt : forall n fr i, In i (cp_rd n fr) -> (i < 50)%nat.
Proof.
  intros n fr i H. unfold cp_rd in H.
  destruct (negb (50 <=? n)); [destruct H|].
  destruct (negb (cp_v fr 12 =? 0x88)); [destruct H as [<-|[]]; lia|].
  destruct (negb (cp_v fr 13 =? 0x19)); [destruct H as [<-|[<-|[]]]; lia|].
  apply in_app_iff in H. destruct H as [H|H]; [apply in_seq in H; lia|].
  destruct (cp_rec fr); [|destruct H].
  destruct (cp_v fr 32 =? 0x12), (cp_kind fr =? 6); cbn in H; intuition lia.
Qed.

Lemma f6_cp_rd_short : forall n fr, n < 50 -> cp_rd n fr = [].
Proof.
  intros n fr H. unfold cp_rd. replace (50 <=? n) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

(* A frame length is never negative. *)
Lemma f6_flen_nn : forall g j, 0 <= flen g j.
Proof.
  intros g j. unfold flen, t_len, f_len, f_L, f_h.
  assert (Hb : forall k, 0 <= inb (g_in g) k) by (intros k; unfold inb; exact (proj1 (bv_unsigned_in_range 8 _))).
  pose proof (Hb (fc (g_in g) j)). pose proof (Hb (fc (g_in g) j + 1)).
  destruct (2 <=? f_left (g_in g) (fc (g_in g) j)); lia.
Qed.

(* The three model flags of a long record that the loop computes. *)
Definition f6_s9 (bs : list byte) : Z :=
  if bv_unsigned (nth 16 bs (Z_to_bv 8 0)) =? 0
  then (if bv_unsigned (nth 17 bs (Z_to_bv 8 0)) =? 0 then 1 else 0) else 0.

Lemma f6_tfill : forall inp j, t_big inp j = true -> b2z (t_tfill inp j) = f6_s9 (t_g inp j).
Proof.
  intros inp j Hb. unfold t_tfill, f6_s9, cp_v, cp_b, cp_z. rewrite Hb. cbn [andb].
  destruct (bv_unsigned (nth 16 (t_g inp j) (Z_to_bv 8 0)) =? 0);
    destruct (bv_unsigned (nth 17 (t_g inp j) (Z_to_bv 8 0)) =? 0); reflexivity.
Qed.

Lemma f6_sum : forall inp j, t_big inp j = true ->
  b2z (t_sum_ok inp j) = (if psum (skipn 18 (t_g inp j)) 32 mod 256 =? 0 then 1 else 0).
Proof.
  intros inp j Hb. unfold t_sum_ok, blocksum. rewrite Hb. cbn [andb].
  destruct (psum (skipn 18 (t_g inp j)) 32 mod 256 =? 0); reflexivity.
Qed.

(* t_8819 is cp_hdr of the record (same boolean). *)
Lemma f6_t8819_hdr : forall inp j, t_8819 inp j = cp_hdr (t_len inp j) (t_g inp j).
Proof. intros inp j. unfold t_8819, t_big, cp_hdr. reflexivity. Qed.

(* The 0x81f40 abort comparison: (snez s8) with s8 = t_k equals the carried [s1+240] = b2z (t_8819). *)
Lemma f6_8819_eq : forall inp j, (if bv_unsigned (Z_to_bv 64 (t_k inp j)) =? 0 then 0 else 1) = b2z (t_8819 inp j).
Proof.
  intros inp j. pose proof (ctrlparse_kind_range (t_len inp j) (t_g inp j)) as HR.
  unfold t_k in *. rewrite unsigned_lit by lia.
  unfold b2z. rewrite f6_t8819_hdr.
  destruct (cp_hdr (t_len inp j) (t_g inp j)) eqn:E.
  - assert (Hne : fst (ctrlparse (t_len inp j) (t_g inp j)) <> 0).
    { intro Z0. apply (proj1 (ctrlparse_none _ _)) in Z0. apply Z0. apply (proj1 (cp_hdr_spec _ _)). exact E. }
    replace (fst (ctrlparse (t_len inp j) (t_g inp j)) =? 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity.
  - assert (H0 : fst (ctrlparse (t_len inp j) (t_g inp j)) = 0).
    { apply ctrlparse_none. rewrite <- cp_hdr_spec. rewrite E. discriminate. }
    rewrite H0. reflexivity.
Qed.

(* The identity_reply argument check of b5_K: four non-null pointers. *)
Lemma f6_reply : forall phi fr, phi <> 0 -> 0 < fr -> reply_args phi (fr + 256) (fr + 272) (fr + 304) = true.
Proof.
  intros phi fr Hphi Hfr. unfold reply_args.
  rewrite (proj2 (Z.eqb_neq phi 0) Hphi).
  rewrite (proj2 (Z.eqb_neq (fr + 256) 0) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (fr + 272) 0) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (fr + 304) 0) ltac:(lia)).
  reflexivity.
Qed.

(* The class-1 side-stack ranges (fp_w1 FS 1) and the class-0 frame base in numbers. *)
Lemma f6_fsh1 : forall FS, fs_hint FS 1 = FS + 8.
Proof. intros FS. unfold fs_hint. cbn. lia. Qed.
Lemma f6_fsf1 : forall FS, fs_flag FS 1 0 = FS + 20480.
Proof. intros FS. unfold fs_flag. cbn. lia. Qed.
Lemma f6_fsM1 : fs_M 1 = 8192.
Proof. reflexivity. Qed.
Lemma f6_fsfr0 : forall FS, fs_frame FS 1 0 = FS + 1085440.
Proof. intros FS. unfold fs_frame, fs_B. cbn. lia. Qed.
Lemma f6_fsfrM : forall FS, fs_frame FS 1 (fs_M 1) = FS + 2134016.
Proof. intros FS. unfold fs_frame, fs_B, fs_M. cbn. lia. Qed.
Lemma f6_afs_flag1 : forall FS j, AC.a_fs_flag FS 1%nat j = FS + 20480 + j.
Proof.
  intros FS j. unfold AC.a_fs_flag.
  change (2 ^ (15 - Z.of_nat 1)) with 16384. change (2 ^ 15) with 32768. lia.
Qed.
Lemma f6_fs_frame0 : forall FS, fs_frame FS 0%nat 0 = FS + 36864.
Proof.
  intros FS. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576.
  change (2 ^ 0) with 1. lia.
Qed.

Lemma f6_fpw1 : forall FS, fp_w [1%nat] FS =
  [(FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016))].
Proof.
  intros FS. unfold fp_w. cbn [flat_map]. rewrite app_nil_r. unfold fp_w1.
  rewrite f6_fsh1, f6_fsf1, f6_fsfrM, f6_fsfr0, f6_fsM1.
  replace (FS + 8 + 8) with (FS + 16) by lia.
  replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

(* The writes of the parse call with o = 0 (its munch list): the stack window, the class-1 side-stack bytes and
   their shadow, and the shadow of the window. *)
Definition f6_PW (S FS : Z) : list ivl :=
  reac_ctrl_parse_fp 0 S ++ fp_w [1%nat] FS ++
  [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)].

Lemma f6_PW_eq : forall S FS, f6_PW S FS =
  [(S - 8800, S); (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   ((FS + 1085440) / 8 + ASAN_K, (FS + 2134016) / 8 + ASAN_K); ((S - 8800) / 8 + ASAN_K, S / 8 + ASAN_K)].
Proof.
  intros S FS. unfold f6_PW, reac_ctrl_parse_fp, fp_w, fp_w1. cbn [flat_map app Z.eqb].
  rewrite f6_fsh1, f6_fsf1, f6_fsfrM, f6_fsfr0, f6_fsM1. unfold shadow_addr, REAC_CTRL_PARSE_K.
  replace (FS + 20480 + 8192) with (FS + 28672) by lia. replace (FS + 8 + 8) with (FS + 16) by lia. reflexivity.
Qed.

(* A contiguous app range lies wholly in the low or wholly in the high app memory. *)
Lemma f6_app_split : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> app_mem a) ->
  hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo.
Proof.
  intros lo hi Hlt H. destruct (Z_le_gt_dec hi LOWMEM_END) as [L|L]; [left; exact L|right].
  destruct (Z_le_gt_dec HIGHMEM_BEG lo) as [L2|L2]; [exact L2|exfalso].
  destruct (Z_le_gt_dec lo LOWMEM_END) as [L3|L3].
  - pose proof (H LOWMEM_END ltac:(lia)) as Ha. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - pose proof (H lo ltac:(lia)) as Ha. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* nth of a tail. *)
Lemma f6_nth_skipn : forall (A : Type) (d : A) (n : nat) (l : list A) (i : nat),
  nth i (skipn n l) d = nth (n + i) l d.
Proof.
  intros A d n. induction n as [|n IH]; intros l i; [reflexivity|].
  destruct l as [|x l]; [cbn; destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

(* mbyte and mrd are the same read. *)
Lemma f6_mbyte_mrd : forall m a, mbyte rsegs m a = mrd rsegs m (wa a).
Proof. intros m a. reflexivity. Qed.

(* The shadow bytes of a contiguous app range are in the shadow. *)
Lemma f6_shadow_ivl : forall lo hi x, (forall a, lo <= a < hi -> app_mem a) -> lo < hi ->
  lo / 8 + ASAN_K <= x < hi / 8 + ASAN_K -> in_shadow x.
Proof.
  intros lo hi x Happ Hlt Hx.
  assert (Hlo : 0 <= lo)
    by (pose proof (Happ lo ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (Hhi : hi <= APPMEM_END)
    by (pose proof (Happ (hi - 1) ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  unfold in_shadow. destruct (f6_app_split lo hi Hlt Happ) as [HL|HH].
  - left. unfold ASAN_K, LOWMEM_END, LOWSHADOW_END in *. Z.div_mod_to_equations. lia.
  - right. unfold ASAN_K, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* An app byte outside the window and outside the three class-1 side-stack ranges is outside the parse writes. *)
Lemma f6_out_PW : forall S FS x,
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - REAC_CTRL_PARSE_K <= a < S -> app_mem a) ->
  REAC_CTRL_PARSE_K <= S -> app_mem x ->
  ~ (S - REAC_CTRL_PARSE_K <= x < S) ->
  ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
  ~ (FS + 1085440 <= x < FS + 2134016) ->
  outside (f6_PW S FS) x.
Proof.
  intros S FS x HFS HW HSK Hx H1 H2 H3 H4. rewrite f6_PW_eq. cbn [outside].
  unfold REAC_CTRL_PARSE_K in H1, HSK.
  split; [intros HC; lia|]. split; [intros HC; lia|]. split; [intros HC; lia|]. split; [intros HC; lia|].
  split.
  { intros HC. apply (app_not_shadow x Hx).
    apply (f6_shadow_ivl (FS + 1085440) (FS + 2134016) x);
      [intros a Ha; apply HFS; unfold FS_SIZE; lia | lia | lia]. }
  split; [|exact I].
  intros HC. apply (app_not_shadow x Hx).
  apply (f6_shadow_ivl (S - 8800) S x);
    [intros a Ha; apply HW; unfold REAC_CTRL_PARSE_K; lia | lia | lia].
Qed.

(* The shadow byte of an app byte apart from the window and from the class-1 frames is outside the parse writes:
   it is not in the four app ranges (it is a shadow byte), and the two shadow ranges of f6_PW are the shadow of
   8-aligned app ranges the byte is apart from. *)
Lemma f6_sh_out : forall S FS p n i,
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - REAC_CTRL_PARSE_K <= a < S -> app_mem a) ->
  REAC_CTRL_PARSE_K <= S -> S mod 8 = 0 -> FS mod 8 = 0 ->
  0 <= i < n -> app_mem (p + i) ->
  (p + n <= S - REAC_CTRL_PARSE_K \/ S <= p) ->
  (p + n <= FS + 1085440 \/ FS + 2134016 <= p) ->
  outside (f6_PW S FS) (shadow_addr (p + i)).
Proof.
  intros S FS p n i HFS HW HSK HS8 HFS8 Hi Hap Hdw Hdf.
  pose proof (shadow_of_app (p + i) Hap) as Hsh.
  rewrite f6_PW_eq. cbn [outside].
  split; [intros HC; exact (app_not_shadow (shadow_addr (p + i))
            (HW (shadow_addr (p + i)) ltac:(unfold REAC_CTRL_PARSE_K; lia)) Hsh)|].
  split; [intros HC; exact (app_not_shadow (shadow_addr (p + i))
            (HFS (shadow_addr (p + i)) ltac:(unfold FS_SIZE; lia)) Hsh)|].
  split; [intros HC; exact (app_not_shadow (shadow_addr (p + i))
            (HFS (shadow_addr (p + i)) ltac:(unfold FS_SIZE; lia)) Hsh)|].
  split; [intros HC; exact (app_not_shadow (shadow_addr (p + i))
            (HFS (shadow_addr (p + i)) ltac:(unfold FS_SIZE; lia)) Hsh)|].
  split.
  { intros HC. unfold shadow_addr, ASAN_K in *. destruct Hdf as [Hd|Hd]; Z.div_mod_to_equations; lia. }
  split; [|exact I].
  intros HC. unfold shadow_addr, ASAN_K, REAC_CTRL_PARSE_K in *. destruct Hdw as [Hd|Hd];
    Z.div_mod_to_equations; lia.
Qed.

(* The class-c flag bytes of a class other than 1 miss the class-1 flag range. *)
Lemma f6_flag_other : forall FS c j, (c <= 10)%nat -> c <> 1%nat -> 0 <= j < AC.a_fs_M c ->
  FS + 4096 <= AC.a_fs_flag FS c j < FS + 36864 /\ ~ (FS + 20480 <= AC.a_fs_flag FS c j < FS + 28672).
Proof.
  intros FS c j Hc Hne Hj. unfold AC.a_fs_flag. unfold AC.a_fs_M in Hj.
  destruct c as [|[|[|[|[|[|[|[|[|[|[|c]]]]]]]]]]];
    try (exfalso; revert Hc Hne; clear; lia);
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj |- *;
    first [ lia | (vm_compute (2 ^ 15) in *; vm_compute in Hj; lia) ].
Qed.

(* a_fs_ok (Contract.v), taken apart once (a Theorem Labs lane's rule for the generated laws: append-only at every nesting level,
   named sub-projections in N+1). Its five conjuncts are found by statement (decompose, then assumption), not by
   position, so a conjunct appended later changes no proof here; every site of this file uses this lemma. *)
Lemma f6_fs_ok_parts : forall (m : word -> option byte) (FS : Z), AC.a_fs_ok m FS ->
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs m a /\ exists b, mbyte rsegs m a = Some b) /\
  word_mem rsegs m (FS + 88) 20 /\ mbyte rsegs m (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs m (AC.a_fs_hint FS c) h) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs m (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/
     mbyte rsegs m (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)).
Proof.
  intros m FS Hok. unfold AC.a_fs_ok in Hok. decompose [and] Hok.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* The side-stack state after the parse run: the class-1 hint word, flag bytes and frames come from the callee's
   fp at return; the hint words and flag bytes of the other classes are unchanged (the run writes only the
   class-1 ranges, their shadow, and the window). *)
Lemma f6_fs_ok_post : forall (m m' : word -> option byte) (S FS TP : Z) (W D : list ivl),
  AC.a_fs_ok m FS ->
  munch (f6_PW S FS) m m' ->
  fp [1%nat] m' TP FS (S - REAC_CTRL_PARSE_K) S W D ->
  REAC_CTRL_PARSE_K <= S ->
  AC.a_fs_ok m' FS.
Proof.
  intros m m' S FS TP W D Hok MU
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFSlo & HAwin & _ & _) HSK.
  destruct (f6_fs_ok_parts m FS Hok) as (_ & _ & _ & HOK4 & HOK5).
  destruct HP as (HFS0 & HFSmod & HFSgt & HFSapp & HSTK).
  pose proof (Forall_inv HCL) as (_ & h1 & flags & Hh1 & Hfl & Hfll & Hflb).
  assert (HFSub : FS + FS_SIZE <= APPMEM_END).
  { pose proof (HFSapp (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as Hh.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HOUT : forall x, FS <= x < FS + FS_SIZE ->
            ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
            ~ (FS + 1085440 <= x < FS + 2134016) -> outside (f6_PW S FS) x).
  { intros x Hx G1 G2 G3.
    apply (f6_out_PW S FS x HFSapp HAwin HSK (HFSapp x Hx)); [|exact G1|exact G2|exact G3].
    lia. }
  split; [|split; [|split; [|split]]].
  - intros a Ha. destruct HSTK as (_ & _ & HS).
    destruct (HS a ltac:(unfold AC.FS_SIZE in Ha; unfold FS_SIZE; lia)) as [Hw (b & Hb)].
    split; [exact Hw | exists b; rewrite f6_mbyte_mrd; exact Hb].
  - pose proof (bytes_at_le8_word rsegs m' (FS + 88) (Z_to_bv 64 20) H88) as HW.
    rewrite MState.unsigned_lit in HW by lia. exact HW.
  - destruct H96 as (_ & _ & H96'). pose proof (H96' 0%nat ltac:(cbn; lia)) as HH.
    cbn [nth_error] in HH. rewrite Z.add_0_r in HH. rewrite f6_mbyte_mrd. exact HH.
  - intros c Hc. destruct (Nat.eq_dec c 1) as [->|Hne].
    + exists (bv_unsigned h1). exact (bytes_at_le8_word rsegs m' (fs_hint FS 1) h1 Hh1).
    + destruct (HOK4 c Hc) as (h & Hh). exists h.
      apply (word_mem_frame rsegs m m' _ _ Hh). intros kk Hk.
      assert (Hhint : AC.a_fs_hint FS c = FS + 8 * Z.of_nat c) by reflexivity.
      unfold mbyte. rewrite MU; [reflexivity|].
      rewrite MState.unsigned_lit by (rewrite Hhint; unfold FS_SIZE, APPMEM_END in *; lia).
      rewrite Hhint. apply HOUT; [unfold FS_SIZE; lia | lia | lia | lia].
  - intros c j Hc Hj. destruct (Nat.eq_dec c 1) as [->|Hne].
    + destruct Hfl as (_ & _ & Hfl').
      assert (Hm8 : AC.a_fs_M 1 = 8192) by (now vm_compute).
      assert (Hlen8 : Z.of_nat (length flags) = 8192) by (rewrite Hfll; now vm_compute).
      rewrite Hm8 in Hj.
      assert (HjN : (Z.to_nat j < length flags)%nat) by lia.
      pose proof (Hfl' (Z.to_nat j) HjN) as HH.
      destruct (nth_error flags (Z.to_nat j)) as [b|] eqn:E;
        [|exfalso; apply nth_error_None in E; lia].
      assert (Eaddr : fs_flag FS 1 0 + Z.of_nat (Z.to_nat j) = AC.a_fs_flag FS 1 j)
        by (unfold fs_flag, AC.a_fs_flag; lia).
      rewrite Eaddr in HH. rewrite f6_mbyte_mrd.
      pose proof (proj1 (Forall_forall _ flags) Hflb b (nth_error_In _ _ E)) as Hb01.
      destruct Hb01 as [->| ->]; [left | right]; exact HH.
    + destruct (f6_flag_other FS c j Hc Hne Hj) as (Hr & Hnot).
      destruct (HOK5 c j Hc Hj) as [HH|HH]; [left|right];
        (unfold mbyte in *; rewrite MU; [exact HH|];
         rewrite MState.unsigned_lit by (unfold FS_SIZE, APPMEM_END in *; lia);
         apply HOUT; [unfold FS_SIZE; lia | lia | exact Hnot | lia]).
Qed.

(* seqz: v_sltiu w 1 is the 0/1 indicator of (w = 0). *)
Lemma f6_seqz : forall w : word, PropExec.v_sltiu w 1 = Z_to_bv 64 (if bv_unsigned w =? 0 then 1 else 0).
Proof.
  intros w. unfold PropExec.v_sltiu. change (bv_wrap 64 1) with 1%Z.
  pose proof (bv_unsigned_in_range 64 w) as Hr. unfold bv_modulus in Hr.
  replace (bv_unsigned w <? 1) with (bv_unsigned w =? 0)
    by (destruct (Z.eqb_spec (bv_unsigned w) 0); destruct (Z.ltb_spec (bv_unsigned w) 1); lia).
  destruct (bv_unsigned w =? 0); reflexivity.
Qed.

(* snez: v_sltu 0 w is the 0/1 indicator of (w <> 0). *)
Lemma f6_snez : forall w : word, PropExec.v_sltu (Z_to_bv 64 0) w = Z_to_bv 64 (if bv_unsigned w =? 0 then 0 else 1).
Proof.
  intros w. unfold PropExec.v_sltu, PropExec.c_ltu, bv_ltu. rewrite unsigned_lit by lia.
  pose proof (bv_unsigned_in_range 64 w) as Hr. unfold bv_modulus in Hr.
  destruct (Z.eqb_spec (bv_unsigned w) 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (0 <? bv_unsigned w) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma f6_land255 : forall x, Z.land x 255 = x mod 256.
Proof. intro x. exact (zb_land_mask x 8 ltac:(lia)). Qed.

Lemma f6_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply unsigned_lit. pose proof (byte_range b). lia. Qed.

(* store_ok from a present (writable) window. *)
Lemma f6_store_ok : forall m m' a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> wview rsegs m (wa (a + i)) <> None) -> wmono rsegs m m' ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' a n H Hw Ha Hn.
  assert (WR : wr_at rsegs m' a (Z.of_nat n)) by (split; [lia|]; split; [lia|]; intros i Hi; apply Hw, H, Hi).
  pose proof (wr_at_store_ok rsegs m' a (Z.of_nat n) 0 n WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* ---------------- the block-sum run 0x81ec0 -> 0x81f54 ---------------- *)

(* The byte-sum loop 0x81ec0 -> 0x81ef8: 32 turns, accumulating a1 = psum over [phi+18, phi+50). Each turn runs the
   instrumented shadow check (a load of the shadow byte at (a >> 3) + ASAN_K and a compare; slow path 0x81eec,
   error 0x82c90 shown NOT reached via addressable m phi 50) then a1 += the byte. *)
Lemma f6_loop : forall (ra0 sp gp tp t0 t1 t2 s0 s1v a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (bs : list byte)
  (Q : machine_state -> Prop),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  (forall a0' a2' a3' a4' a5' : word,
     LE.evt rsegs Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0'
         (Z_to_bv 64 (psum (skipn 18 bs) 32)) a2' a3' a4' a5' a6 a7
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81ef8) fc None m (seg_rom rsegs))) ->
  forall n i (a4' a5' : word), (i + n = 32)%nat -> (0 < n)%nat ->
  LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 18 + Z.of_nat i))
         (Z_to_bv 64 (psum (skipn 18 bs) i)) (Z_to_bv 64 (phi + 18 + Z.of_nat i))
         (Z_to_bv 64 (32 - Z.of_nat i)) a4' a5' a6 a7
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81ec0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 Fr fc m phi bs Q
    Hphi0 Hphi50 Hlen HB HA Hjoin.
  induction n as [|n IH]; intros i a4' a5' Hin Hn; [lia|].
  (* shadow check of the byte at phi+18+i *)
  assert (Haddr1 : addressable m (phi + 18 + Z.of_nat i) 1).
  { replace (phi + 18 + Z.of_nat i) with (phi + (18 + Z.of_nat i)) by lia.
    apply (addressable_sub m phi 50 (18 + Z.of_nat i) 1 HA); lia. }
  destruct (sl_shadow1 m (phi + 18 + Z.of_nat i) Haddr1) as (sb & RDsb & OKsb & ISsb).
  pose proof (rd_byte rsegs m phi bs (18 + i)%nat HB ltac:(lia)) as RDb.
  replace (Z.of_nat (18 + i)) with (18 + Z.of_nat i) in RDb by lia.
  replace (phi + (18 + Z.of_nat i)) with (phi + 18 + Z.of_nat i) in RDb by lia.
  pose proof (psum_range (skipn 18 bs) i) as PR. change (Z.of_nat 32) with 32 in PR.
  (* the join at 0x81ed0 (shadow passed), with the slow-path register a5 generalized *)
  assert (G38 : forall y5 : word,
    LE.evt rsegs Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 18 + Z.of_nat i))
       (Z_to_bv 64 (psum (skipn 18 bs) i)) (Z_to_bv 64 (phi + 18 + Z.of_nat i))
       (Z_to_bv 64 (32 - Z.of_nat i)) (sxb sb) y5 a6 a7
       s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x81ed0) fc None m (seg_rom rsegs))).
  { intro y5.
    step. (* lbu a4,0(a2) *)
    step. (* addi a3,a3,-1 *)
    step. (* addi a0,a0,1 *)
    step. (* add a1,a1,a4 *)
    rewrite <- (f6_nth_skipn byte (Z_to_bv 8 0) 18 bs i).
    rewrite psum_S_zxb.
    step. (* addi a2,a2,1 *)
    step. (* bnez a3,81ec0 *)
    destruct n as [|n'].
    - (* last turn: a3 = 0, not taken; fall to 0x81ee8 -> 0x81ef8 *)
      replace i with 31%nat in * by lia.
      replace (32 - Z.of_nat 31) with 1 by lia. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
      step. (* j 81ef8 *)
      apply Hjoin.
    - (* more turns: a3 = 32-(i+1) <> 0, taken back to 0x81ec0 at i+1 *)
      replace (32 - Z.of_nat i + -1) with (32 - Z.of_nat (S i)) by lia.
      rewrite (rc_neq0_64 (32 - Z.of_nat (S i))) by lia. cbn [negb]. cbv iota.
      replace (phi + 18 + Z.of_nat i + 1) with (phi + 18 + Z.of_nat (S i)) by lia.
      apply (IH (S i)); lia. }
  (* run the shadow check 0x81ec0-0x81ecc *)
  step. (* srli a4,a0,3 *)
  step. (* add a4,a4,s10 *)
  rewrite (unsigned_lit (phi + 18 + Z.of_nat i)) by lia.
  step. (* lb a4,0(a4) : a4 = sxb sb (RDsb) *)
  step. (* bnez a4,81eec *)
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb)) by (pose proof (rc_byte_signed sb); lia).
  destruct (Z.eqb_spec (bv_signed sb) 0) as [Z0|Z0].
  - (* shadow 0: not taken, fall to 0x81ed0 *)
    cbn [negb]. cbv iota. apply (G38 a5').
  - (* shadow <> 0: slow path 0x81eec *)
    cbn [negb]. cbv iota.
    step. (* andi a5,a0,7 *)
    rewrite (unsigned_lit (phi + 18 + Z.of_nat i)) by lia. rewrite rc_land7.
    step. (* bge a5,a4,82c90 *)
    unfold sxb. rewrite (rc_lts_signed ((phi + 18 + Z.of_nat i) mod 8) (bv_signed sb))
      by (pose proof (rc_byte_signed sb); pose proof (Z.mod_pos_bound (phi + 18 + Z.of_nat i) 8 ltac:(lia)); lia).
    replace ((phi + 18 + Z.of_nat i) mod 8 <? bv_signed sb) with true
      by (symmetry; apply Z.ltb_lt; destruct OKsb as [H|H]; lia).
    cbn [negb]. cbv iota.
    step. (* j 81ed0 *)
    apply (G38 (Z_to_bv 64 ((phi + 18 + Z.of_nat i) mod 8))).
Qed.

(* The run 0x81ec0 -> 0x81f54 over explicit registers: the 32-byte sum loop, the two instrumented byte checks of
   phi+16 / phi+17 (slow paths 0x82a38 / 0x82ab0 shown NOT reached), s9 = (byte16 = 0 and byte17 = 0), the abort
   compare at 0x81f40 shown NOT taken ([s1+240] = e240 = (s8 <> 0)), and the store [s1+280] = (low byte of the
   sum = 0). s8 = v8 (the parse kind), s7 = phi, s1 = A. *)
Lemma f6_e28_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 a4i a5i a6 a7 s3 s4i s5 s6 s9i s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi A tlen v8 e240 : Z) (bs : list byte),
    0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
    bytes_at rsegs m phi bs -> addressable m phi 50 ->
    0 <= A -> A + 288 <= 2 ^ 64 -> stk rsegs m (A + 240) (A + 288) ->
    0 <= v8 < 2 ^ 64 -> q64 m (A + 240) e240 -> e240 = (if v8 =? 0 then 0 else 1) ->
    LE.evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0' a1' a2' a3' a4' a5' a6 a7
                       (Z_to_bv 64 tlen) s3 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 0 else 1)) s5 s6
                       (Z_to_bv 64 phi) (Z_to_bv 64 v8) (Z_to_bv 64 (f6_s9 bs)) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81f54) fc None
                  (write_to_mem m (wa (A + 280)) (le8 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 1 else 0))))
                  (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 0)
               (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 32) a4i a5i a6 a7
               (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ec0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a4i a5i a6 a7 s3 s4i s5 s6 s9i s11 t3 t4 t5 t6 Fr fc m phi A tlen v8 e240 bs
    Hphi0 Hphi50 Hlen HB HA HA0 HA288 Hstk Hv8 Hq240 He240.
  match goal with |- LE.evt _ ?Q _ => set (QE := Q) end.
  (* the two byte-check / abort / store tail 0x81ef8 -> 0x81f54, as the loop join *)
  assert (Htail : forall a0' a2' a3' a4' a5' : word,
    LE.evt rsegs QE (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0'
       (Z_to_bv 64 (psum (skipn 18 bs) 32)) a2' a3' a4' a5' a6 a7
       (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x81ef8) fc None m (seg_rom rsegs))).
  { intros a0' a2' a3' a4' a5'.
    assert (Ha16 : addressable m (phi + 16) 1)
      by (apply (addressable_sub m phi 50 16 1 HA); lia).
    destruct (sl_shadow1 m (phi + 16) Ha16) as (sb16 & RD16 & OK16 & IS16).
    pose proof (rd_byte rsegs m phi bs 16 HB ltac:(lia)) as RDb16. change (Z.of_nat 16) with 16 in RDb16.
    assert (Ha17 : addressable m (phi + 17) 1)
      by (apply (addressable_sub m phi 50 17 1 HA); lia).
    destruct (sl_shadow1 m (phi + 17) Ha17) as (sb17 & RD17 & OK17 & IS17).
    pose proof (rd_byte rsegs m phi bs 17 HB ltac:(lia)) as RDb17. change (Z.of_nat 17) with 17 in RDb17.
    pose proof (bytes_at_ov_read rsegs m (A + 240) (le8 (Z_to_bv 64 e240)) 0 8 Hq240 ltac:(rewrite length_le8; lia)) as RD240.
    cbn [Z.of_nat] in RD240. rewrite Z.add_0_r, skipn_O, firstn_all2 in RD240 by (rewrite length_le8; lia).
    assert (HS280 : store_ok rsegs m (wa (A + 280)) 8 = true).
    { apply (f6_store_ok m m (A + 280) 8); [|apply wmono_refl|lia|lia].
      intros kk Hk. destruct Hstk as (_ & _ & Hs). destruct (Hs (A + 280 + kk) ltac:(lia)) as [Hw _]. exact Hw. }
    pose proof (psum_range (skipn 18 bs) 32) as PRsum. change (Z.of_nat 32) with 32 in PRsum.
    (* the join at 0x81f38 (after both byte checks), dead a0/a2/a3/a4/a5 generalized, s9 the model flag *)
    assert (GA0 : forall a0v a2v a3v a4v a5v s9v : word, s9v = Z_to_bv 64 (f6_s9 bs) ->
      LE.evt rsegs QE (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0v
         (Z_to_bv 64 (psum (skipn 18 bs) 32)) a2v a3v a4v a5v a6 a7
         (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9v (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81f38) fc None m (seg_rom rsegs))).
    { intros a0v a2v a3v a4v a5v s9v Hs9v. subst s9v.
      step. (* snez a0,s8 *)
      rewrite f6_snez, (unsigned_lit v8) by lia.
      step. (* ld a2,240(s1) *)
      step. (* bne a0,a2 : not taken (e240 = (v8<>0)) *)
      rewrite He240, bv_eqb_refl. cbn [negb]. cbv iota.
      step. (* zext.b a0,a1 *)
      rewrite (unsigned_lit (psum (skipn 18 bs) 32)) by lia. rewrite f6_land255.
      step. (* seqz a1,a0 *)
      rewrite f6_seqz, (unsigned_lit (psum (skipn 18 bs) 32 mod 256))
        by (pose proof (Z.mod_pos_bound (psum (skipn 18 bs) 32) 256 ltac:(lia)); lia).
      step. (* sd a1,280(s1) *)
      step. (* snez s4,a0 *)
      rewrite f6_snez, (unsigned_lit (psum (skipn 18 bs) 32 mod 256))
        by (pose proof (Z.mod_pos_bound (psum (skipn 18 bs) 32) 256 ltac:(lia)); lia).
      unfold QE. apply evt_done. do 6 eexists. reflexivity. }
    (* the join at 0x81f0c (byte16 shadow passed), dead a3 generalized *)
    assert (G74 : forall a3v : word,
      LE.evt rsegs QE (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 16))
         (Z_to_bv 64 (psum (skipn 18 bs) 32)) (sxb sb16) a3v a4' a5' a6 a7
         (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81f0c) fc None m (seg_rom rsegs))).
    { intro a3v.
      step. (* lbu a0,0(a0) : byte16 *)
      step. (* beqz a0,81f1c *)
      unfold zxb. rewrite (rc_eqb0_signed (bv_unsigned (nth 16 bs (Z_to_bv 8 0))))
        by (pose proof (byte_range (nth 16 bs (Z_to_bv 8 0))); lia).
      destruct (Z.eqb_spec (bv_unsigned (nth 16 bs (Z_to_bv 8 0))) 0) as [B16|B16].
      - (* byte16 = 0: beqz taken to 0x81f1c, check byte17, s9 = seqz byte17 *)
        cbv iota.
        step. step. step. rewrite (unsigned_lit (phi + 17)) by lia. step. (* addi;srli;add;lb a2 (phi+17) *)
        step. (* bnez a2,82ab0 *)
        unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb17)) by (pose proof (rc_byte_signed sb17); lia).
        assert (G98 : forall a3w : word,
          LE.evt rsegs QE (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 17))
             (Z_to_bv 64 (psum (skipn 18 bs) 32)) (sxb sb17) a3w a4' a5' a6 a7
             (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
           Fr (Z_to_bv 64 0x81f30) fc None m (seg_rom rsegs))).
        { intro a3w.
          step. (* lbu a0,0(a0) : byte17 *)
          step. (* seqz s9,a0 *)
          rewrite f6_seqz. apply GA0.
          unfold f6_s9. rewrite B16, Z.eqb_refl. rewrite ?f6_zxb_u.
          rewrite ?(unsigned_lit (bv_unsigned (nth 17 bs (Z_to_bv 8 0))))
            by (pose proof (byte_range (nth 17 bs (Z_to_bv 8 0))); lia).
          reflexivity. }
        destruct (Z.eqb_spec (bv_signed sb17) 0) as [Z17|Z17].
        + cbn [negb]. cbv iota. apply (G98 a3v).
        + cbn [negb]. cbv iota.
          step. (* andi a3,a0,7 *)
          rewrite (unsigned_lit (phi + 17)) by lia. rewrite rc_land7.
          step. (* bge a3,a2,82d2c *)
          unfold sxb. rewrite (rc_lts_signed ((phi + 17) mod 8) (bv_signed sb17))
            by (pose proof (rc_byte_signed sb17); pose proof (Z.mod_pos_bound (phi + 17) 8 ltac:(lia)); lia).
          replace ((phi + 17) mod 8 <? bv_signed sb17) with true
            by (symmetry; apply Z.ltb_lt; destruct OK17 as [H|H]; lia).
          cbn [negb]. cbv iota. step. (* j 81f30 *)
          apply (G98 (Z_to_bv 64 ((phi + 17) mod 8))).
      - (* byte16 <> 0: beqz not taken, 0x81f14 li s9,0 ; j 81f38 *)
        cbv iota.
        step. (* li s9,0 *)
        step. (* j 81f38 *)
        apply GA0. unfold f6_s9. rewrite (proj2 (Z.eqb_neq _ 0) B16). reflexivity. }
    (* run 0x81ef8-0x81f08: compute phi+16 and its shadow check *)
    step. step. step. rewrite (unsigned_lit (phi + 16)) by lia. step. (* addi;srli;add;lb a2 (phi+16) *)
    step. (* bnez a2,82a38 *)
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb16)) by (pose proof (rc_byte_signed sb16); lia).
    destruct (Z.eqb_spec (bv_signed sb16) 0) as [Z16|Z16].
    - cbn [negb]. cbv iota. apply (G74 a3').
    - cbn [negb]. cbv iota.
      step. (* andi a3,a0,7 *)
      rewrite (unsigned_lit (phi + 16)) by lia. rewrite rc_land7.
      step. (* bge a3,a2,82cfc *)
      unfold sxb. rewrite (rc_lts_signed ((phi + 16) mod 8) (bv_signed sb16))
        by (pose proof (rc_byte_signed sb16); pose proof (Z.mod_pos_bound (phi + 16) 8 ltac:(lia)); lia).
      replace ((phi + 16) mod 8 <? bv_signed sb16) with true
        by (symmetry; apply Z.ltb_lt; destruct OK16 as [H|H]; lia).
      cbn [negb]. cbv iota. step. (* j 81f0c *)
      apply (G74 (Z_to_bv 64 ((phi + 16) mod 8))). }
  (* step into the loop at i = 0 and discharge the join with Htail *)
  replace (Z_to_bv 64 (phi + 18)) with (Z_to_bv 64 (phi + 18 + Z.of_nat 0)) by (f_equal; lia).
  replace (Z_to_bv 64 0) with (Z_to_bv 64 (psum (skipn 18 bs) 0)) by reflexivity.
  replace (Z_to_bv 64 32) with (Z_to_bv 64 (32 - Z.of_nat 0)) by (f_equal; lia).
  apply (f6_loop ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a6 a7 (Z_to_bv 64 tlen) s3 s4i s5 s6
           (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i s11 t3 t4 t5 t6 Fr fc m phi bs QE
           Hphi0 Hphi50 Hlen HB HA Htail 32 0 a4i a5i eq_refl ltac:(lia)).
Qed.

(* ---------------- memory transports ---------------- *)

(* addressable survives a run whose writes miss the shadow bytes of the range. *)
Lemma f6_addr_keep : forall W m m' p n,
  addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact (HW i Hi).
Qed.

(* One byte of an addressable range. *)
Lemma f6_addr1 : forall m p n a, addressable m p n -> p <= a < p + n -> addressable m a 1.
Proof.
  intros m p n a (H0 & Hn & Hhi & Hall) Hx.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + i) with (p + (a - p + i)) by lia. apply Hall. lia.
Qed.

(* Two bv literals in range are equal only if their values are. *)
Lemma f6_id : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal (@bv_unsigned 64)) in E.
  rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.

(* An 8-byte cell survives a write whose footprint misses it. *)
Lemma f6_q64_keep : forall W m m' a v, q64 m a v -> munch W m m' ->
  (forall x, a <= x < a + 8 -> outside W x) -> q64 m' a v.
Proof.
  intros W m m' a v H MU HW. unfold q64 in *.
  apply (fl_bytes W m m' a (le8 (Z_to_bv 64 v)) H MU).
  rewrite length_le8. exact HW.
Qed.

(* A thread word survives a write whose footprint misses its eight bytes, and is read back unchanged. *)
Lemma f6_word_eq : forall W m m' a, munch W m m' ->
  (forall x, a <= x < a + 8 -> outside W x) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  forall v, word_mem rsegs m a v <-> word_mem rsegs m' a v.
Proof.
  intros W m m' a MU HW Ha Hhi v.
  assert (HE : forall k, (k < 8)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))).
  { intros k Hk. apply MU. rewrite MState.unsigned_lit by lia. apply HW; lia. }
  split; intros H k Hk; pose proof (H k Hk) as Hb; unfold mbyte in *.
  - rewrite (HE k Hk). exact Hb.
  - rewrite (HE k Hk) in Hb. exact Hb.
Qed.

(* A frame-loop spill word survives a write that misses its eight bytes. The spill's own existential base names
   the same A as FRA: the cell is inside [A, A + 416) and A is far below 2 ^ 64, so no other representative of
   register 9 can name that cell. *)
Lemma f6_spill_keep : forall regs regs' A off v m m' W,
  spill regs m off v -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= APPMEM_END -> 0 <= off <= 408 ->
  getr regs' 9 = getr regs 9 -> munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' A off v m m' W HS H9 HA HAE Hoff E9 MU HW.
  destruct HS as (A' & H9' & Hq).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HP : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Hqb : 0 <= A' + off /\ A' + off + Z.of_nat (length (le8 (Z_to_bv 64 v))) <= 2 ^ 64)
    by (unfold q64 in Hq; exact (bytes_at_bound rsegs m (A' + off) _ Hq)).
  rewrite length_le8 in Hqb.
  assert (HAA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm.
    assert (Hdz : (A' - A) mod 2 ^ 64 = 0).
    { rewrite Zminus_mod, Hm, Z.sub_diag. apply Zmod_0_l. }
    destruct (proj1 (Zmod_divides (A' - A) (2 ^ 64) ltac:(lia)) Hdz) as (q & Hq2).
    rewrite HP in Hq2. lia. }
  subst A'.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  exact (f6_q64_keep W m m' (A + off) v Hq MU HW).
Qed.

(* An interval of the prologue save area is application memory. *)
Lemma f6_app_ivl : forall lo hi, HIGHMEM_BEG <= lo -> hi <= APPMEM_END -> app_ivl lo hi.
Proof. intros lo hi H1 H2 a Ha. unfold app_mem. right. lia. Qed.

(* The shadow of an app-range address is below HIGHMEM_BEG. *)
Lemma f6_sh_hi : forall a, a <= APPMEM_END -> shadow_addr a <= HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; unfold APPMEM_END in *; lia).
  lia.
Qed.

Lemma f6_sh_lo : forall a, 0 <= a -> LOWMEM_END <= shadow_addr a.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, LOWMEM_END.
  assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
Qed.

(* Every registered global lies in the image, below AC.GT: checked by computation over AF.frame_AG. *)
Definition f6_ag_ok : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? AC.GT)) AF.frame_AG.

Lemma f6_ag_true : f6_ag_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f6_ag_lt : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & n & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) f6_ag_true (lo, n) Hin) as H.
  apply andb_prop in H as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2. cbn in H1, H2. lia.
Qed.

(* The six BC bytes the bcmp wrapper compares with are the registered global (REAC_CTRL_PARSE_BC, 7) (.str.4:
   v1.8 0x211e0, v1.9 0x21200). The entry is found in AF.frame_AG by search, so the proof names neither the
   address nor the entry's position in the list. *)
Lemma f6_bc_addr : forall m, (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  addressable m REAC_CTRL_PARSE_BC 6.
Proof.
  intros m HAG.
  assert (Hin : In (REAC_CTRL_PARSE_BC, 7) AF.frame_AG)
    by (unfold REAC_CTRL_PARSE_BC, AF.frame_AG; repeat (first [apply in_eq | apply in_cons])).
  assert (Hlo : 0 <= REAC_CTRL_PARSE_BC < 2 ^ 32) by (unfold REAC_CTRL_PARSE_BC; lia).
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
  intros i Hi.
  assert (Hg : in_globals AF.frame_AG (REAC_CTRL_PARSE_BC + i))
    by (exists REAC_CTRL_PARSE_BC, 7; split; [exact Hin | lia]).
  destruct (HAG _ Hg) as (_ & _ & _ & H). specialize (H 0 ltac:(lia)). rewrite Z.add_0_r in H. exact H.
Qed.

(* ---------------- the normalized memory (MemNorm) ---------------- *)

(* Above the image there is no read-only byte, so normalizing changes nothing there. *)
Definition f6_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma f6_tops_gt : f6_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f6_find_below : forall segs top x n s,
  f6_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold f6_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma f6_ro_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (f6_find_below sg 0x5fe000 x n s f6_tops_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma f6_stk_iff : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi HR Hlo Hhi.
  split; intros (H0 & H1 & H); (split; [exact H0|]); (split; [exact H1|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb);
    pose proof (wview_rel_rw rsegs m m0 (wa a) HR (f6_ro_hi a ltac:(lia))) as EW;
    pose proof (mrd_rel rsegs m m0 (wa a) HR) as ER.
  - split; [rewrite EW; exact Hw | exists b; rewrite <- ER; exact Hb].
  - split; [rewrite <- EW; exact Hw | exists b; rewrite ER; exact Hb].
Qed.

Lemma f6_sw_iff : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 HR.
  split; intros H a Ha; pose proof (in_shadow_range a Ha) as Hr;
    pose proof Ha as Ha'; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha';
    destruct (H a Ha) as (Hw & b & Hb);
    pose proof (wview_rel_rw rsegs m m0 (wa a) HR (f6_ro_hi a ltac:(lia))) as EW;
    pose proof (mrd_rel rsegs m m0 (wa a) HR) as ER.
  - split; [rewrite EW; exact Hw | exists b; rewrite <- ER; exact Hb].
  - split; [rewrite <- EW; exact Hw | exists b; rewrite ER; exact Hb].
Qed.

Lemma f6_addr_iff : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n HR.
  split; intros (H0 & H1 & H2 & H); (split; [exact H0|]); (split; [exact H1|]); (split; [exact H2|]);
    intros i Hi; destruct (H i Hi) as (Hap & b & Hb & Hok); (split; [exact Hap|]); exists b;
    pose proof (mrd_rel rsegs m m0 (wa (shadow_addr (p + i))) HR) as ER.
  - rewrite <- ER. split; [exact Hb | exact Hok].
  - rewrite ER. split; [exact Hb | exact Hok].
Qed.

Lemma f6_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (proj1 (bytes_at_rel rsegs m m0 a bs R) ltac:(assumption)) end.
Qed.

Lemma f6_tls_tr : forall m m0 TP DT TS C T DB k,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells m0 TP DT TS C T DB k.
Proof.
  intros m m0 TP DT TS C T DB k R H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15
                 & H16 & H17 & HDB & H19).
  unfold asan_tls_cells.
  split; [exact (R _ _ H1)|]. split; [exact (R _ _ H2)|]. split; [exact (R _ _ H3)|].
  split; [exact (R _ _ H4)|]. split; [exact (R _ _ H5)|]. split; [exact Hk|].
  split; [exact (R _ _ H7)|]. split; [exact (R _ _ H8)|]. split; [exact (R _ _ H9)|].
  split; [exact (R _ _ H10)|]. split; [exists tb, te; exact (R _ _ H11)|].
  split; [exact (R _ _ H12)|]. split; [exact (R _ _ H13)|]. split; [exact (R _ _ H14)|].
  split; [exact (R _ _ H15)|]. split; [exact (R _ _ H16)|]. split; [exact (R _ _ H17)|].
  split; [exact HDB|]. exact (R _ _ H19).
Qed.

Lemma f6_fp_tr : forall cs m m0 TP FS lo hi W D,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  (forall lo' hi', 0x5fe000 <= lo' -> hi' <= 2 ^ 64 -> stk rsegs m lo' hi' -> stk rsegs m0 lo' hi') ->
  fp cs m TP FS lo hi W D -> fp cs m0 TP FS lo hi W D.
Proof.
  intros cs m m0 TP FS lo hi W D Hba Hstk
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact (f6_tls_tr m m0 _ _ _ _ _ _ _ Hba HT)|].
  split; [exact (Hba _ _ HTP)|].
  split.
  { destruct HP as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    split; [exact P4|]. pose proof P5 as P5'. destruct P5' as (_ & P5b & _).
    apply Hstk; [unfold ASAN_GT in P3; lia | exact P5b | exact P5]. }
  split; [exact (Hba _ _ H88)|].
  split; [exact (Hba _ _ H96)|].
  split.
  { eapply Forall_impl; [|exact HCL]. intros c (Hc & h & fl & Hh & Hfl & Hfll & Hflb).
    split; [exact Hc|]. exists h, fl. split; [exact (Hba _ _ Hh)|]. split; [exact (Hba _ _ Hfl)|].
    split; [exact Hfll | exact Hflb]. }
  split; [exact HFS|]. split; [exact HA|]. split; [exact HWd | exact HDd].
Qed.

Lemma f6_fp_iff : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  (fp cs m TP FS lo hi W D <-> fp cs m0 TP FS lo hi W D).
Proof.
  intros cs m m0 TP FS lo hi W D HR. split; apply f6_fp_tr.
  - intros a bs H. exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) H).
  - intros lo' hi' H1 H2 H. exact (proj1 (f6_stk_iff m m0 lo' hi' HR H1 H2) H).
  - intros a bs H. exact (proj2 (bytes_at_rel rsegs m m0 a bs HR) H).
  - intros lo' hi' H1 H2 H. exact (proj2 (f6_stk_iff m m0 lo' hi' HR H1 H2) H).
Qed.

Lemma f6_tls_iff : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k HR. split; apply f6_tls_tr; intros a bs H.
  - exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) H).
  - exact (proj2 (bytes_at_rel rsegs m m0 a bs HR) H).
Qed.

(* ---------------- helpers of the side-stack bundle (F9's f9_fp_call, for reac_ctrl_parse) ---------------- *)

Lemma f6_dj_pt : forall (Q : Z -> Prop) a b c d, a < b -> c < d ->
  (forall x, a <= x < b -> Q x) -> (forall x, c <= x < d -> ~ Q x) -> RcLay.ly_dj a b c d.
Proof.
  intros Q a b c d Hab Hcd HQ HnQ. unfold RcLay.ly_dj.
  destruct (Z_le_gt_dec b c) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec d a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (HnQ (Z.max a c) ltac:(lia)). apply HQ. lia.
Qed.

Lemma f6_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma f6_word_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia.
Qed.

Lemma f6_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (f6_byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs).
  { rewrite bytes_le_to_Z_le_val. exact (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2 ^ 8)%Z.
    change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma f6_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by (cbn; lia).
  rewrite <- L at 1. apply f6_le_bytes_to_Z.
Qed.

(* A single present byte is a one-byte bytes_at. *)
Lemma f6_byte_at : forall m a b, 0 <= a -> a + 1 <= 2 ^ 64 -> mbyte rsegs m a = Some b ->
  bytes_at rsegs m a [b].
Proof.
  intros m a b H0 H1 Hb. split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
  cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact Hb.
Qed.

(* A range of present bytes, all satisfying P, is a bytes_at of a list of that length. *)
Lemma f6_bytes_PN : forall (P : byte -> Prop) m a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = k /\ Forall P bs.
Proof.
  intros P m a k. revert a. induction k as [|k IH]; intros a H0 H1 H.
  - exists []. split; [|split; [reflexivity | constructor]].
    split; [exact H0|]. split; [cbn [length]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - destruct (H 0 ltac:(lia)) as (b & Hb & HPb).
    assert (Hrec : forall i, 0 <= i < Z.of_nat k -> exists b', mbyte rsegs m (a + 1 + i) = Some b' /\ P b').
    { intros i Hi. destruct (H (1 + i) ltac:(lia)) as (b' & Hb' & HP'). exists b'.
      split; [|exact HP']. replace (a + 1 + i) with (a + (1 + i)) by lia. exact Hb'. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrec) as (bs & Hbs & Hlen & HPbs).
    exists (b :: bs). split; [|split; [cbn [length]; lia | constructor; assumption]].
    destruct Hbs as (_ & _ & Hnth).
    split; [exact H0|]. split; [cbn [length]; rewrite Hlen; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + replace (a + Z.of_nat 0) with (a + 0) by lia. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hnth. cbn [length] in Hi. lia.
Qed.

Lemma f6_bytes_P : forall (P : byte -> Prop) m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ Z.of_nat (length bs) = n /\ Forall P bs.
Proof.
  intros P m a n H0 Hn H1 H.
  destruct (f6_bytes_PN P m a (Z.to_nat n) H0 ltac:(rewrite Z2Nat.id by lia; lia)
              ltac:(rewrite Z2Nat.id by lia; exact H)) as (bs & Hbs & Hlen & HP).
  exists bs. split; [exact Hbs|]. split; [rewrite Hlen, Z2Nat.id by lia; reflexivity | exact HP].
Qed.

(* Eight present bytes read as some word. *)
Lemma f6_word_present : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b) ->
  exists w : word, bytes_at rsegs m a (le8 w).
Proof.
  intros m a H0 H1 H.
  assert (HP : forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b /\ True).
  { intros i Hi. destruct (H i Hi) as (b & Hb). exists b. split; [exact Hb | exact I]. }
  destruct (f6_bytes_P (fun _ => True) m a 8 H0 ltac:(lia) H1 HP) as (bs & Hbs & Hlen & _).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite f6_le8_of_bytes by lia. exact Hbs.
Qed.

(* word_mem pins the value only modulo 2^64. *)
Lemma f6_word_mem_eq : forall m a v1 v2, word_mem rsegs m a v1 -> word_mem rsegs m a v2 ->
  v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (E : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (EB : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    rewrite <- (kb_byte_unsigned v1 8 k), <- (kb_byte_unsigned v2 8 k), EB. reflexivity. }
  assert (M : forall v k, le_byte (v mod 2 ^ 64) 8 k = le_byte v 8 k).
  { intros v k. unfold le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
  pose proof (kb_le8_digits (v1 mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as D1.
  pose proof (kb_le8_digits (v2 mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as D2.
  rewrite !M in D1. rewrite !M in D2.
  rewrite D1 at 1. rewrite D2 at 1.
  rewrite (E 0%nat ltac:(lia)), (E 1%nat ltac:(lia)), (E 2%nat ltac:(lia)), (E 3%nat ltac:(lia)),
    (E 4%nat ltac:(lia)), (E 5%nat ltac:(lia)), (E 6%nat ltac:(lia)), (E 7%nat ltac:(lia)).
  reflexivity.
Qed.

Lemma f6_wm_norm : forall m a x y, word_mem rsegs m a x -> word_mem rsegs m a y ->
  0 <= y < 2 ^ 64 -> - (2 ^ 64) < x < 2 ^ 64 -> x = y \/ x = y - 2 ^ 64.
Proof.
  intros m a x y Hx Hy Hy0 Hx0.
  pose proof (f6_word_mem_eq m a x y Hx Hy) as E.
  rewrite (Z.mod_small y (2 ^ 64)) in E by lia.
  destruct (Z_le_gt_dec 0 x) as [Hs|Hs].
  - left. rewrite (Z.mod_small x (2 ^ 64)) in E by lia. exact E.
  - right.
    assert (EM : (x + 2 ^ 64) mod 2 ^ 64 = x mod 2 ^ 64).
    { replace (x + 2 ^ 64) with (x + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full. }
    rewrite (Z.mod_small (x + 2 ^ 64) (2 ^ 64)) in EM by lia. lia.
Qed.

(* Each disjointness leaf names image constants, FS / fr / sp offsets and shadow endpoints: unfold the constants
   and let lia use the range facts of the context. *)
Ltac f6_num :=
  cbv [RcLay.ly_dj TLS_INDEX REAL_TLS_GET_ADDR TSD_KEY_INITED TSD_KEY GOT_CF CF GOT_VERBOSITY VERBOSITY DTLS_TPOFF
       RT_TP RT_TSDMAIN RT_GT ASAN_GT AC.as_tp AC.ASYMS AC.GT AC.FS_SIZE FS_SIZE RT_FS_SIZE
       REAC_CTRL_PARSE_K AF.SLOT_STACK HIGHMEM_BEG APPMEM_END LOWMEM_END LOWSHADOW_END HIGHSHADOW_BEG
       ASAN_K] in *; lia.

Ltac f6_dj_split := repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd].

(* mkR_of regs is the explicit 31-slot register map. *)
Lemma f6_mkR_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot to its carried value. *)
Ltac f6_slot H := let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* A machine state with no pending syscall is the MS of its own fields. *)
Lemma f6_ms_eta : forall ms, ms_svc_pending ms = None ->
  ms = MS (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros ms H. destruct ms. cbn in H. subst. reflexivity. Qed.

(* One byte of a carried byte list, as a one-byte cell. *)
Lemma f6_byte1 : forall m a bs (i : nat) b, bytes_at rsegs m a bs -> nth_error bs i = Some b ->
  bytes_at rsegs m (a + Z.of_nat i) [b].
Proof.
  intros m a bs i b (H0 & H1 & H) Hn.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. destruct k as [|k]; [|lia].
  cbn [nth_error]. replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) by lia.
  rewrite H by exact Hi. exact Hn.
Qed.

(* The runtime cells the bcmp wrapper of reac_ctrl_parse reads, from FRA's AsanRTInv.RT alone: the real
   bcmp / memcmp addresses, the GOT word of the CF table and its two flag bytes. *)
Lemma f6_rt_cells : forall sp m md, AsanRTInv.RT sp m md ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp m md HRT.
  pose proof (AsanRTInv.RT_real_cells sp m md HRT) as HR.
  pose proof (AsanRTInv.RT_cf_cells sp m md HRT) as (Hg & _ & _ & _ & _ & _ & H240 & _).
  split; [exact (AsanRTInv.real_cell_of m REAL_BCMP BCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact (AsanRTInv.real_cell_of m REAL_MEMCMP MEMCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact Hg|].
  split.
  - pose proof (f6_byte1 m (RT_CF + 240) _ 14 (Z_to_bv 8 1) H240 eq_refl) as HH.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in HH by (unfold RT_CF, CF; lia). exact HH.
  - pose proof (f6_byte1 m (RT_CF + 240) _ 15 (Z_to_bv 8 1) H240 eq_refl) as HH.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in HH by (unfold RT_CF, CF; lia). exact HH.
Qed.

(* The identity record of every turn is ID_SIZE = 38 bytes: ID0 is, and each ingest keeps the length
   (RcIdentModel.ING_length). *)
Lemma f6_tID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  assert (Hturn : forall s len g, length (fs_id s) = 38%nat -> length (fs_id (turn s len g)) = 38%nat).
  { intros s len g Hs.
    assert (Hr : length (rp_id (fs_id s) len g) = 38%nat).
    { unfold rp_id. destruct (RcReply.ir len g); [exact (RcIdentModel.ING_length _ _ _ Hs) | exact Hs]. }
    unfold turn. cbv zeta. unfold fg_id.
    destruct (f_opens len g); cbn [fs_id];
      (destruct (fg_rf len (fs_fg s) g =? 1); [exact (RcIdentModel.ING_length _ _ _ Hr) | exact Hr]). }
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  cbn [fst_at]. exact (Hturn _ _ _ IH).
Qed.

(* IDj (the 38 identity bytes at fr + 2688, inside the frame body) across a write that misses the frame. *)
Lemma f6_idj_keep : forall g fr j W mem mem', IDj g fr j mem -> munch W mem mem' ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x) -> IDj g fr j mem'.
Proof.
  intros g fr j W mem mem' (Hb & Hok) MU Ofr. pose proof FRAME_BYTES_val as HFBv. split; [|exact Hok].
  unfold IDBe in *. apply (fl_bytes W mem mem' (fr + 2688) (t_ID (g_in g) j) Hb MU).
  rewrite f6_tID_len. intros x Hx. apply Ofr. lia.
Qed.

(* A prefix of a carried byte list is carried. *)
Lemma f6_bytes_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n (H0 & H1 & H). pose proof (length_firstn n bs) as HL.
  split; [exact H0|]. split; [lia|].
  intros i Hi. rewrite (H i ltac:(lia)).
  rewrite <- (firstn_skipn n bs) at 1. apply nth_error_app1. lia.
Qed.

(* The memcmp model reads only the first n bytes of each side. *)
Lemma f6_memcmp_firstn : forall n l r, SFA.memcmp_model (firstn n l) (firstn n r) n = SFA.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r]; cbn; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

(* A slice is at most as long as its count, and a turn's record bytes at most its length. *)
Lemma f6_bsl_len : forall bs k n, (length (RcFrag.bsl bs k n) <= Z.to_nat n)%nat.
Proof. intros bs k n. unfold RcFrag.bsl. rewrite length_firstn. lia. Qed.
Lemma f6_tphi_len : forall g j, (length (t_phi (g_in g) j) <= Z.to_nat (flen g j))%nat.
Proof. intros g j. unfold flen, t_phi, t_len, f_phi. rewrite length_firstn. lia. Qed.
(* The first-fragment body of the model state (v1.9 SlotModel.turn): at most block[9 ..] of a 50-byte record. *)
Lemma f6_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  cbn [fst_at]. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn, f6_tg_len. lia.
Qed.

(* The 0x88 0x19 record test implies the long arm. *)
Lemma f6_8819_big : forall g j, t_8819 (g_in g) j = true -> 50 <= flen g j.
Proof.
  intros g j H. unfold flen, t_8819 in *.
  apply andb_prop in H. destruct H as (H & _). apply andb_prop in H. destruct H as (H & _).
  unfold t_big in H. apply Z.leb_le in H. exact H.
Qed.

(* Z.shiftr a 3 + ASAN_K is the shadow address of a. *)
Lemma f6_shiftr_shadow : forall a, Z.shiftr a 3 + ASAN_K = shadow_addr a.
Proof. intros a. unfold shadow_addr. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* b5_PF (push 14 groups C / E) across a write that misses the save area below [A + 280), the frame body and
   the record block, with the shadow bytes of the last two. The byte lists whose length the text leaves open
   (the 38-byte record prefix and the two 6-byte compare operands) are re-witnessed by their `firstn`, which
   the memcmp model does not see. *)
Lemma f6_pf_keep : forall g j phi fr A regs regs' mem mem' W,
  b5_PF g j phi fr regs mem -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 < 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> munch W mem mem' ->
  0 <= phi -> phi + AC.a_size (flen g j) <= APPMEM_END ->
  (forall x, A <= x < A + 280 -> outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x /\ outside W (shadow_addr x)) ->
  (forall x, phi <= x < phi + AC.a_size (flen g j) -> outside W x /\ outside W (shadow_addr x)) ->
  b5_PF g j phi fr regs' mem'.
Proof.
  intros g j phi fr A regs regs' mem mem' W (A1 & H9a & HA1 & Hrec & H88) H9 HA HA4 E9 MU Hphi0 HphiE
    OA Ofr Oph. pose proof FRAME_BYTES_val as HFBv.
  rewrite (f6_id A1 A HA1 HA ltac:(unfold rg in H9a, H9; rewrite <- H9a; exact H9)) in *.
  assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite E9; exact H9).
  assert (Hq : forall off v, 0 <= off <= 272 -> q64 mem (A + off) v -> q64 mem' (A + off) v).
  { intros off v Hoff Hqv. unfold q64 in *. apply (fl_bytes W mem mem' (A + off) _ Hqv MU).
    rewrite length_le8. intros x Hx. apply OA. lia. }
  assert (Hblk : forall a bs, phi <= a -> a + Z.of_nat (length bs) <= phi + AC.a_size (flen g j) ->
      bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs).
  { intros a bs Ha Hb Hbs. apply (fl_bytes W mem mem' a bs Hbs MU).
    intros x Hx. exact (proj1 (Oph x ltac:(lia))). }
  assert (Hfrm : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
      bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs).
  { intros a bs Ha Hb Hbs. apply (fl_bytes W mem mem' a bs Hbs MU).
    intros x Hx. exact (proj1 (Ofr x ltac:(lia))). }
  assert (Hsh : forall a, phi <= a < phi + AC.a_size (flen g j) ->
      b8 mem (Z.shiftr a 3 + ASAN_K) 0 -> b8 mem' (Z.shiftr a 3 + ASAN_K) 0).
  { intros a Ha Hb. unfold b8 in *. apply (fl_bytes W mem mem' _ _ Hb MU).
    cbn [length]. intros x Hx. replace x with (Z.shiftr a 3 + ASAN_K) by lia.
    rewrite f6_shiftr_shadow. exact (proj2 (Oph a Ha)). }
  exists A. split; [exact H9'|]. split; [exact HA|].
  split.
  { intros Hlen.
    assert (Esz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
    destruct (Hrec Hlen) as ((rb & Hrb & Hrbl) & Htphi).
    split.
    { exists (firstn 38 rb). split.
      - exact (Hblk phi (firstn 38 rb) ltac:(lia) ltac:(rewrite length_firstn; lia)
                 (f6_bytes_firstn mem phi rb 38 Hrb)).
      - rewrite length_firstn. lia. }
    pose proof (f6_tphi_len g j) as HL.
    exact (Hblk phi (t_phi (g_in g) j) ltac:(lia) ltac:(lia) Htphi). }
  intros H8819. pose proof (f6_8819_big g j H8819) as Hbig.
  assert (Esz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  destruct (H88 H8819) as
    ((field16 & v14 & v15 & v16 & v17 & Hu16 & Hb14 & Hb15 & Hb16 & Hb17 &
      Hr14 & Hr15 & Hr16 & Hr17 & Hs14 & Hs15 & Hs16 & Hs17 & Hf16 & Hzz) &
     (ls & rs & Hq72 & Hls & Hlsl & Hrs & Hrsl & Hcmp & Had186) &
     (ls2 & rs2 & Hq64 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcmp2 & Had180)).
  split.
  { exists field16, v14, v15, v16, v17.
    split.
    { exact (Hfrm (fr + 176 + 20) (le2 (Z_to_bv 64 field16)) ltac:(lia)
               ltac:(rewrite length_le2; lia) Hu16). }
    split; [exact (Hblk (phi + 14) [Z_to_bv 8 v14] ltac:(lia) ltac:(cbn [length]; lia) Hb14)|].
    split; [exact (Hblk (phi + 15) [Z_to_bv 8 v15] ltac:(lia) ltac:(cbn [length]; lia) Hb15)|].
    split; [exact (Hblk (phi + 16) [Z_to_bv 8 v16] ltac:(lia) ltac:(cbn [length]; lia) Hb16)|].
    split; [exact (Hblk (phi + 17) [Z_to_bv 8 v17] ltac:(lia) ltac:(cbn [length]; lia) Hb17)|].
    split; [exact Hr14|]. split; [exact Hr15|]. split; [exact Hr16|]. split; [exact Hr17|].
    split; [exact (Hsh (phi + 14) ltac:(lia) Hs14)|].
    split; [exact (Hsh (phi + 15) ltac:(lia) Hs15)|].
    split; [exact (Hsh (phi + 16) ltac:(lia) Hs16)|].
    split; [exact (Hsh (phi + 17) ltac:(lia) Hs17)|].
    split; [exact Hf16 | exact Hzz]. }
  split.
  { exists (firstn 6 ls), (firstn 6 rs).
    split; [exact (Hq 72 (fr + 186) ltac:(lia) Hq72)|].
    split.
    { exact (Hfrm (fr + 186) (firstn 6 ls) ltac:(lia) ltac:(rewrite length_firstn; lia)
               (f6_bytes_firstn mem (fr + 186) ls 6 Hls)). }
    split; [rewrite length_firstn; lia|].
    split.
    { exact (Hblk phi (firstn 6 rs) ltac:(lia) ltac:(rewrite length_firstn; lia)
               (f6_bytes_firstn mem phi rs 6 Hrs)). }
    split; [rewrite length_firstn; lia|].
    split; [rewrite f6_memcmp_firstn; exact Hcmp|].
    apply (f6_addr_keep W mem mem' (fr + 186) 6 Had186 MU).
    intros i Hi. exact (proj2 (Ofr (fr + 186 + i) ltac:(lia))). }
  exists (firstn 6 ls2), (firstn 6 rs2).
  split; [exact (Hq 64 (fr + 180) ltac:(lia) Hq64)|].
  split.
  { exact (Hfrm (fr + 180) (firstn 6 ls2) ltac:(lia) ltac:(rewrite length_firstn; lia)
             (f6_bytes_firstn mem (fr + 180) ls2 6 Hls2)). }
  split; [rewrite length_firstn; lia|].
  split.
  { exact (Hblk (phi + 6) (firstn 6 rs2) ltac:(lia) ltac:(rewrite length_firstn; lia)
             (f6_bytes_firstn mem (phi + 6) rs2 6 Hrs2)). }
  split; [rewrite length_firstn; lia|].
  split; [rewrite f6_memcmp_firstn; exact Hcmp2|].
  apply (f6_addr_keep W mem mem' (fr + 180) 6 Had180 MU).
  intros i Hi. exact (proj2 (Ofr (fr + 180 + i) ltac:(lia))).
Qed.


Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The callee contract (plan-asan section 4 PARSE), a Section Hypothesis as the brief prescribes. *)
Hypothesis HPARSE : reac_ctrl_parse_contract.

(* ---------------- frame_facts and the generated laws, each taken apart once ----------------
   a Theorem Labs lane's rule for the generated laws (append-only at every nesting level; named sub-projections come in N+1):
   each law's list is taken apart in ONE lemma below, and every site of this file uses that lemma. An inner
   destruct pattern ends in `_`, so a conjunct appended later lands there. A conjunct needed from the END of a list
   is never named by position: the list is decomposed into all its conjuncts and the goal is closed by assumption
   (or the hypothesis is found by its statement). *)

(* frame_facts (SlotInv.v): the image's segments and the three sink cells the callee bundle names. *)
Lemma f6_ff : ms_segs B = rsegs /\ @sk_ofl_head SH = 0x5fbf08 /\ @sk_ofl_lock SK = 0x5fbf00 /\
  @sk_threaded SK = 0x5fbaa0 + 1.
Proof.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  exact (conj SEGS (conj Hhead (conj Hlock Hthr))).
Qed.

(* a_laws_thread: the TSD main word C and the thread record T at C + 152, the ownership and app-memory facts of the
   8 bytes at C + 152, and the ownership and presence of the 16 bytes at T + 48. *)
Lemma f6_thread : forall H mem md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  exists C T, word_mem rsegs mem RT_TSDMAIN C /\ 0 < C < 2 ^ 64 /\ 0 < T < 2 ^ 64 /\
    word_mem rsegs mem (C + 152) T /\
    (forall i, 0 <= i < 8 ->
       AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (C + 152 + i) /\ app_mem (C + 152 + i)) /\
    (forall i, 0 <= i < 16 ->
       AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (T + 48 + i) /\
       exists b, mbyte rsegs mem (T + 48 + i) = Some b).
Proof.
  intros H mem md HAH.
  destruct (AC.a_laws_thread _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md HAH)
    as (_ & _ & _ & C & T & HCw & HCr & HTr & HTw & HC152 & _ & _ & _ & _ & _ & _ & _ & _ & HT48 & _).
  exists C, T.
  split; [exact HCw|]. split; [exact HCr|]. split; [exact HTr|]. split; [exact HTw|].
  split; intros i Hi; [pose proof (HC152 i Hi) as L | pose proof (HT48 i Hi) as L];
    decompose [and] L; split; assumption.
Qed.

(* a_laws_fs_state: a_fs_ok at the base FS; the thread's DTLS word DB at tp + 8, whose word at DB + 24 is tp and
   whose 8 bytes there are app memory below stklo and off the side stack; the 16 bytes at T + 48 are app memory. *)
Lemma f6_fs_state : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.a_fs_ok mem FS /\
  (exists DB, 0 <= DB < 2 ^ 64 /\ word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) DB /\
     word_mem rsegs mem (DB + 24) (AC.as_tp AC.ASYMS) /\
     forall a, DB + 24 <= a < DB + 32 ->
       app_mem a /\ a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ AC.a_in_fs AC.ASYMS mem a) /\
  (forall C T, word_mem rsegs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem rsegs mem (C + 152) T ->
     0 <= T < 2 ^ 64 -> forall i, 0 <= i < 16 -> app_mem (T + 48 + i)).
Proof.
  intros H mem md FS HAH Htp HFS.
  pose proof (AC.a_laws_fs_state _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Htp HFS)
    as L.
  decompose [and ex] L.
  split; [assumption|]. split; [|assumption].
  match goal with Hw : word_mem _ _ (AC.as_tp AC.ASYMS + 8) ?DB |- _ => exists DB end.
  split; [lia|]. split; [assumption|]. split; [assumption|].
  intros a Ha.
  match goal with HP : forall a, _ + 24 <= a < _ + 32 -> _ |- _ =>
    destruct (HP a Ha) as (Happ & Hlo & _ & Hnfs & _) end.
  exact (conj Happ (conj Hlo Hnfs)).
Qed.

(* a_laws_fs_place: the side stack [FS, FS + FS_SIZE) is above GT, below stklo, page-aligned and app memory. *)
Lemma f6_fs_place : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ FS mod 4096 = 0 /\
  forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a.
Proof.
  intros H mem md FS HAH Htp HFS.
  pose proof (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Htp HFS)
    as L.
  decompose [and] L. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* a_laws_not_owned, for the two ranges this file reads: a side-stack byte and a byte of [stklo, APPMEM_END) are
   not the runtime's. *)
Lemma f6_not_owned : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  AC.a_in_fs AC.ASYMS mem a \/ AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a.
Proof.
  intros H mem md a HAH Ha.
  destruct (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md a HAH
              ltac:(tauto)) as (Hno & _).
  exact Hno.
Qed.

(* a_laws_blocks: a live block (p, n) starts at or above 4096 and ends at or below stklo, and each of its bytes is
   app memory off the side stack. *)
Lemma f6_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a.
Proof.
  intros H mem md p n HAH Hin.
  pose proof (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md p n HAH Hin) as L.
  decompose [and] L. split; [assumption|]. split; [assumption|].
  intros a Ha.
  match goal with Hall : forall a, p <= a < p + n -> _ |- _ => pose proof (Hall a Ha) as La end.
  decompose [and] La. split; assumption.
Qed.

(* a_laws_store: a store that keeps every byte off a_store_ok and keeps writability keeps AH, the runtime's
   ownership, stklo and stkhi. *)
Lemma f6_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hagree Hwm.
  pose proof (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hagree Hwm)
    as L.
  decompose [and] L. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* a_laws_fs_store: the same for a run that also writes the side stack and its shadow, when the side stack's
   state stays a_fs_ok. *)
Lemma f6_fs_store : forall H mem mem' md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md FS HAH Htp HFS Hagree Hwm Hok.
  pose proof (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                H mem mem' md FS HAH Htp HFS Hagree Hwm Hok) as L.
  decompose [and] L. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* Any sub-range of the 416-byte prologue save area [A, A + 416) is byte-backed and writable: it lies inside
   FRA's entry-anchored slot window, because g_S g - 4096 < sp <= A and A + 416 <= g_S g. *)
Lemma f6_spill_stk : forall g fr hb regs mem md A lo hi,
  FRA B APIf ra g fr hb regs mem md -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  A <= lo -> lo <= hi -> hi <= A + 416 -> stk rsegs mem lo hi.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md A lo hi HFRA Hr9 HA Hlo Hmid Hhi.
  pose proof HFRA as HF. destruct HF as (A' & sp & s5 & H).
  assert (Hr9' : rg regs 9 A') by tauto.
  assert (Hsp : sp <= A') by tauto.
  assert (HAS : A' <= g_S g) by tauto.
  assert (HS4 : g_S g - 4096 < sp) by tauto.
  assert (HA416 : A' + 416 <= g_S g) by tauto.
  assert (Hstk : stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g)) by tauto.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof Hstk as Hstk'. unfold stk in Hstk'. destruct Hstk' as (Hb0 & Hb1 & _).
  assert (HA' : 0 <= A' < 2 ^ 64) by lia.
  assert (EA : A = A').
  { pose proof (rg_eq64 regs 9 A A' Hr9 Hr9') as Hm.
    rewrite (Z.mod_small A (2 ^ 64)) in Hm by lia. rewrite (Z.mod_small A' (2 ^ 64)) in Hm by lia. exact Hm. }
  subst A'.
  destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) lo (g_S g) Hstk ltac:(lia)) as (_ & H1).
  destruct (stk_split rsegs mem lo hi (g_S g) H1 ltac:(lia)) as (H2 & _). exact H2.
Qed.

(* The run 0x81f54 -> 0x81f64 over explicit registers: the three argument moves and the parse call composed with
   its contract (o = 0). The contract asks for mem_inv, so it runs on MemNorm.normalize m: every premise below
   crosses mem_rel (the window, the shadow and the side stack are above the image, the other cells are bytes_at
   facts), and the post comes back to the real memory through evt_normalize's ms_rel and ro_same. *)
Lemma f6_ebc_evt :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n S FS : Z) (bs : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    asan_cells m -> shadow_rw m ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S) (reac_ctrl_parse_D f n 0) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81f64) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1v
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81f64) fc None m' (seg_rom rsegs) /\
         munch (f6_PW S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S)
           (reac_ctrl_parse_D f n 0))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6 Fr fc m f n S FS bs
    Hf Hn HS HS16 HHI HAPP HST HRO Hlen Hbig HRD HAC HSW HWA HFA HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (HSKl : 0x5fe000 <= S - REAC_CTRL_PARSE_K) by (unfold HIGHMEM_BEG in HHI; lia).
  (* the premises on the normalized memory *)
  pose proof (proj1 (f6_stk_iff m (normalize rsegs m) (S - REAC_CTRL_PARSE_K) S REL HSKl ltac:(lia)) HST)
    as HSTn.
  pose proof (mem_inv_normalize rsegs m) as HMIn.
  assert (HRDn : forall i, In i (cp_rd n bs) ->
            mrd rsegs (normalize rsegs m) (wa (f + Z.of_nat i)) = nth_error bs i).
  { intros i Hi. rewrite <- (mrd_rel rsegs m _ _ REL). exact (HRD i Hi). }
  pose proof (f6_cells_rel m _ REL HAC) as HACn.
  pose proof (proj1 (f6_sw_iff m _ REL) HSW) as HSWn.
  pose proof (proj1 (f6_addr_iff m _ _ _ REL) HWA) as HWAn.
  assert (HFAn : 50 <= n -> addressable (normalize rsegs m) f 50)
    by (intros Hb; exact (proj1 (f6_addr_iff m _ _ _ REL) (HFA Hb))).
  pose proof (proj1 (f6_addr_iff m _ _ _ REL) HBC) as HBCn.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H1) as H1n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H2) as H2n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H3) as H3n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H4) as H4n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H5) as H5n.
  pose proof (proj1 (f6_fp_iff _ m _ _ _ _ _ _ _ REL) HFP) as HFPn.
  assert (HTLSn : reac_ctrl_parse_tls (normalize rsegs m) (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S).
  { intros DT TS C T DB k HT. apply HTLS. exact (proj2 (f6_tls_iff m _ _ _ _ _ _ _ _ REL) HT). }
  clear HST HRD HAC HSW HWA HFA HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* 0x81f54 mv a0,s7 ; 0x81f58 mv a1,s2 ; 0x81f5c li a2,0 ; 0x81f60 jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof HPARSE as HP. unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE in HP.
  eapply LE.evt_cut.
  { eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact HRO |].
    eapply HP with (f := f) (n := n) (o := 0) (S := S) (FS := FS) (fr := bs) (junk := []).
    all: try reflexivity.
    all: try assumption.
    all: try lia.
    all: try (intros Ho; exfalso; apply Ho; reflexivity). }
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E & MU & WM & MI & ST & _ & ACm & SR & AD & FP & _) & HREL & HROs).
  subst s0'.
  destruct HREL as (Er & Ef & Epc & Esvc & Erv & Efc & Erom & Hrel).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in Er, Ef, Epc, Esvc, Erv,
    Efc, Erom, Hrel.
  set (mm' := ms_mem ms') in Hrel, HROs.
  rewrite (f6_ms_eta ms' Esvc), Er, Ef, Epc, Erv, Efc, Erom.
  apply LE.evt_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mm'.
  split.
  { replace (ret_pc (Z_to_bv 64 0x81f64)) with (Z_to_bv 64 0x81f64)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    reflexivity. }
  split; [exact (munch_rel rsegs (f6_PW S FS) m (normalize rsegs m) mm' m0' REL Hrel HROs MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) mm' m0' REL Hrel HROs WM)|].
  split; [exact (ro_agree_same rsegs m mm' HRO HROs)|].
  split; [exact (proj2 (f6_stk_iff mm' m0' (S - REAC_CTRL_PARSE_K) S Hrel HSKl ltac:(lia)) ST)|].
  split; [exact (proj2 (f6_sw_iff mm' m0' Hrel) SR)|].
  split; [exact (proj2 (f6_addr_iff mm' m0' _ _ Hrel) AD)|].
  exact (proj2 (f6_fp_iff _ mm' m0' _ _ _ _ _ _ Hrel) FP).
Qed.

(* The callee's side-stack bundle, built at the call (F9's f9_fp_call for reac_ctrl_parse's W / D lists): the
   FakeStack base FS is the word at tp (RT_fs_cells), its state comes from a_laws_fs_state, the thread cells from
   RT_uw_cells / a_laws_thread, the DTLS word from b5_FS; every cell fp names is apart from the callee's window
   (the window is at or above stklo, the cells below it), and the record block is apart from the class-1
   side-stack ranges (a_laws_blocks: no block byte is in the FakeStack). The callee's W is its window only
   (o = 0), so the frame's placement is not needed. *)
Lemma f6_fp_call : forall g fr phi len regs mem md,
  FRA B APIf ra g fr [(phi, AC.a_size len)] regs mem md -> b5_FS fr mem ->
  exists FS,
    word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
    fp [1%nat] mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_PARSE_K) (AC.aspZ regs)
      (reac_ctrl_parse_W 0 (AC.aspZ regs)) (reac_ctrl_parse_D phi len 0) /\
    reac_ctrl_parse_tls mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_PARSE_K) (AC.aspZ regs).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr phi len regs mem md HFRA (_ & DBp & HDBp & HDBp0 & HDBp1).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  rewrite Haspz.
  assert (HspA : sp <= APPMEM_END) by lia.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  (* ---- the side stack's base FS ---- *)
  destruct (AsanRTInv.RT_fs_cells _ _ _ HRT)
    as (Htlsidx & Hdtpoff & Hdt & Hdt8 & (FSw & HFSb & HFSok) & (DBw & HDBb & HDBnz)).
  pose proof (bytes_at_le8_word rsegs mem RT_TP FSw HFSb) as HFSwm.
  remember (bv_unsigned FSw) as FS eqn:EFS.
  assert (HFS64 : 0 <= FS < 2 ^ 64) by (rewrite EFS; apply f6_word_range).
  destruct HFSok as (HFSpos & HFSalign & HFSgt & HFSapp).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as NSTK1.
  destruct (f6_fs_place _ _ _ _ HAH HFSwm HFS64) as (_ & NFS1 & _ & _).
  destruct (f6_fs_state _ _ _ _ HAH HFSwm HFS64) as (Hfsok & (DBz & _ & HDBzw & HDBztp & HDBzp) & HT48app).
  destruct (f6_fs_ok_parts _ _ Hfsok) as (HFSpres & HFS88 & HFS96 & _ & HFSflag).
  assert (NAPP : APPMEM_END < 2 ^ 64) by (unfold APPMEM_END; lia).
  assert (NFSB : FS + 11571200 <= APPMEM_END)
    by (unfold AC.FS_SIZE in NFS1; unfold AF.SLOT_STACK in Hstklo; lia).
  (* ---- the thread record (f6_thread) ---- *)
  destruct (f6_thread _ _ _ HAH) as (C0 & T0 & HC0wm & HC0rng & HT0rng & HT0wm & HC152 & HT48).
  destruct (AsanRTInv.RT_uw_cells _ _ _ HRT) as (Htsdi & Htsdk & _ & Htp88 & (Cw & HCwb)).
  pose proof (bytes_at_le8_word rsegs mem RT_TSDMAIN Cw HCwb) as HCwm.
  assert (ECw : bv_unsigned Cw = C0).
  { pose proof (f6_word_range Cw) as HR.
    destruct (f6_wm_norm mem RT_TSDMAIN (bv_unsigned Cw) C0 HCwm HC0wm ltac:(lia) ltac:(lia)) as [E|E];
      [exact E | lia]. }
  assert (HCapp : forall x, C0 + 152 <= x < C0 + 160 -> app_mem x).
  { intros x Hx. pose proof (proj2 (HC152 (x - (C0 + 152)) ltac:(lia))) as H.
    replace (C0 + 152 + (x - (C0 + 152))) with x in H by lia. exact H. }
  assert (HCpt : forall x, C0 + 152 <= x < C0 + 160 ->
            x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HC152 (x - (C0 + 152)) ltac:(lia)) as (Hown & Hap).
    replace (C0 + 152 + (x - (C0 + 152))) with x in Hown by lia.
    pose proof (HCapp x Hx) as Hax.
    split.
    - destruct (Z_lt_le_dec x (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END)
        by (unfold APPMEM_END; lia).
      exact (f6_not_owned _ _ _ x HAH (or_intror Hst) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x)
        by (exists FS; split; [exact HFS64 | split; [exact HFSwm | exact Hin]]).
      exact (f6_not_owned _ _ _ x HAH (or_introl HFSin) Hown). }
  assert (HTapp : forall x, T0 + 48 <= x < T0 + 64 -> app_mem x).
  { intros x Hx.
    pose proof (HT48app C0 T0 HC0wm ltac:(lia) HT0wm ltac:(lia) (x - (T0 + 48)) ltac:(lia)) as H.
    replace (T0 + 48 + (x - (T0 + 48))) with x in H by lia. exact H. }
  assert (HTpt : forall x, T0 + 48 <= x < T0 + 64 ->
            x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HT48 (x - (T0 + 48)) ltac:(lia)) as (Hown & _).
    replace (T0 + 48 + (x - (T0 + 48))) with x in Hown by lia.
    pose proof (HTapp x Hx) as Hax.
    split.
    - destruct (Z_lt_le_dec x (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END)
        by (unfold APPMEM_END; lia).
      exact (f6_not_owned _ _ _ x HAH (or_intror Hst) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x)
        by (exists FS; split; [exact HFS64 | split; [exact HFSwm | exact Hin]]).
      exact (f6_not_owned _ _ _ x HAH (or_introl HFSin) Hown). }
  assert (HTpres : forall i, 0 <= i < 16 -> exists b, mbyte rsegs mem (T0 + 48 + i) = Some b).
  { intros i Hi. exact (proj2 (HT48 i Hi)). }
  (* ---- the thread's DTLS word ---- *)
  assert (EDBz : DBz = DBp).
  { pose proof (proj1 (HDBzp (DBz + 24) ltac:(lia))) as Ha1.
    pose proof (proj1 (HDBzp (DBz + 31) ltac:(lia))) as Ha2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha1, Ha2.
    destruct (f6_wm_norm mem (AC.as_tp AC.ASYMS + 8) DBz DBp HDBzw HDBp ltac:(lia) ltac:(lia)) as [E|E];
      [exact E | lia]. }
  assert (EDBw : bv_unsigned DBw = DBp).
  { pose proof (f6_word_range DBw) as HR.
    pose proof (bytes_at_le8_word rsegs mem (RT_TP + 8) DBw HDBb) as HDBwm.
    destruct (f6_wm_norm mem (AC.as_tp AC.ASYMS + 8) (bv_unsigned DBw) DBp HDBwm HDBp ltac:(lia) ltac:(lia))
      as [E|E]; [exact E | lia]. }
  assert (HDBpt : forall x, DBp + 24 <= x < DBp + 32 ->
            app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
            ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. rewrite <- EDBz in Hx. destruct (HDBzp x Hx) as (H1 & H2 & H4).
    split; [exact H1|]. split; [exact H2|]. intros Hin. apply H4.
    exists FS. split; [exact HFS64 | split; [exact HFSwm | exact Hin]]. }
  assert (HDB24 : bytes_at rsegs mem (bv_unsigned DBw + 24) (le8 (Z_to_bv 64 (AC.as_tp AC.ASYMS)))).
  { rewrite EDBw, <- EDBz.
    apply (word_mem_le8 rsegs mem (DBz + 24) (AC.as_tp AC.ASYMS) HDBztp);
      [cbv [AC.as_tp AC.ASYMS]; lia | lia | lia]. }
  (* ---- numeric bounds of the thread cells ---- *)
  assert (NC0 : C0 + 160 <= APPMEM_END).
  { pose proof (HCapp (C0 + 159) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NT0 : T0 + 64 <= APPMEM_END).
  { pose proof (HTapp (T0 + 63) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NC : C0 + 160 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (HCpt (C0 + 159) ltac:(lia))); lia).
  assert (NT : T0 + 64 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (HTpt (T0 + 63) ltac:(lia))); lia).
  assert (NDB : DBp + 32 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (proj2 (HDBpt (DBp + 31) ltac:(lia)))); lia).
  (* ---- the words the tls cells name ---- *)
  assert (EDTu : bv_unsigned (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) = AC.as_tp AC.ASYMS + 32)
    by (apply MState.unsigned_lit; cbv [AC.as_tp AC.ASYMS]; lia).
  assert (ETSu : bv_unsigned (Z_to_bv 64 RT_TSDMAIN) = RT_TSDMAIN)
    by (apply MState.unsigned_lit; unfold RT_TSDMAIN; lia).
  assert (ETu : bv_unsigned (Z_to_bv 64 T0) = T0) by (apply MState.unsigned_lit; lia).
  pose proof (word_mem_le8 rsegs mem (C0 + 152) T0 HT0wm ltac:(lia) ltac:(lia)
                ltac:(unfold APPMEM_END in *; lia)) as HT0b.
  destruct (f6_word_present mem (T0 + 48) ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
      ltac:(intros i Hi; exact (HTpres i ltac:(lia)))) as (tb & Htb).
  assert (HTpres2 : forall i, 0 <= i < 8 -> exists b, mbyte rsegs mem (T0 + 56 + i) = Some b).
  { intros i Hi. replace (T0 + 56 + i) with (T0 + 48 + (8 + i)) by lia. exact (HTpres (8 + i) ltac:(lia)). }
  destruct (f6_word_present mem (T0 + 56) ltac:(lia) ltac:(unfold APPMEM_END in *; lia) HTpres2) as (te & Hte).
  assert (HTBE : bytes_at rsegs mem (T0 + 48) (le8 tb ++ le8 te)).
  { apply (proj2 (bytes_at_app rsegs mem (T0 + 48) (le8 tb) (le8 te))).
    split; [exact Htb|]. rewrite length_le8.
    replace (T0 + 48 + Z.of_nat 8) with (T0 + 56) by lia. exact Hte. }
  destruct (AsanRTInv.RT_cf_cells _ _ _ HRT) as (Hcf1 & _ & _ & _ & _ & Hcf137 & _ & _).
  destruct (AsanRTInv.RT_opt_cells _ _ _ HRT) as (_ & _ & Hopt3 & Hopt4).
  pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HREAL.
  assert (HTLS : asan_tls_cells mem (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                   (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0).
  { unfold asan_tls_cells. rewrite EDTu, ETSu, ETu, ECw.
    split; [exact Htlsidx|].
    split; [exact (AsanRTInv.real_cell_of mem REAL_TLS_GET_ADDR MUSL_TLS_GET_ADDR HREAL
                     ltac:(vm_compute; reflexivity))|].
    split; [exact Hdt|].
    split; [exact Hdt8|].
    split; [exact Htsdi|].
    split; [lia|].
    split; [exact Htsdk|].
    split; [exact Htp88|].
    split; [exact HCwb|].
    split; [exact HT0b|].
    split; [exists tb, te; exact HTBE|].
    split; [exact Hcf1|].
    split; [exact Hcf137|].
    split; [exact Hopt3|].
    split; [exact Hopt4|].
    split; [exact Hdtpoff|].
    split; [exact HDBb|].
    split; [exact (proj1 HDBnz)|].
    exact HDB24. }
  (* ---- app memory and shadow memory are apart ---- *)
  assert (HGAP : forall x, LOWMEM_END <= x < HIGHMEM_BEG -> ~ app_mem x).
  { intros x Hx Hap. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (AS_C : RcLay.ly_dj (C0 + 152) (C0 + 160) LOWMEM_END HIGHMEM_BEG).
  { apply (f6_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HCapp | exact HGAP]. }
  assert (AS_T : RcLay.ly_dj (T0 + 48) (T0 + 64) LOWMEM_END HIGHMEM_BEG).
  { apply (f6_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HTapp | exact HGAP]. }
  assert (AS_DB : RcLay.ly_dj (DBp + 24) (DBp + 32) LOWMEM_END HIGHMEM_BEG).
  { apply (f6_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
    | intros x Hx; exact (proj1 (HDBpt x Hx)) | exact HGAP]. }
  (* ---- the shadow of the class-1 frames and of the callee's window lies between the app ranges ---- *)
  assert (SB1a : LOWMEM_END <= shadow_addr (FS + 1085440)) by (apply f6_sh_lo; lia).
  assert (SB1b : shadow_addr (FS + 2134016) <= HIGHMEM_BEG)
    by (apply f6_sh_hi; unfold APPMEM_END in *; lia).
  assert (SB2a : LOWMEM_END <= shadow_addr (sp - REAC_CTRL_PARSE_K)).
  { apply f6_sh_lo. unfold REAC_CTRL_PARSE_K, AF.SLOT_STACK, HIGHMEM_BEG in *. lia. }
  assert (SB2b : shadow_addr sp <= HIGHMEM_BEG) by (apply f6_sh_hi; lia).
  (* ---- the thread cells are apart from the side stack ---- *)
  assert (DJ_C_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (C0 + 152) (C0 + 160)).
  { apply (f6_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (HCpt x Hx)). }
  assert (DJ_T_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (T0 + 48) (T0 + 64)).
  { apply (f6_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (HTpt x Hx)). }
  assert (DJ_DB_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (DBp + 24) (DBp + 32)).
  { apply (f6_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (proj2 (HDBpt x Hx))). }
  (* ---- the heap block of the parse record ---- *)
  assert (HPHI : 50 <= len -> forall x, phi <= x < phi + 50 ->
            app_mem x /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros Hlen x Hx.
    destruct (f6_blocks _ _ _ phi (AC.a_size len) HAH ltac:(apply in_or_app; left; left; reflexivity))
      as (_ & _ & Hb).
    destruct (Hb x ltac:(unfold AC.a_size; lia)) as (Hap & Hnfs).
    split; [exact Hap|]. intros Hin. apply Hnfs.
    exists FS. split; [exact HFS64 | split; [exact HFSwm | exact Hin]]. }
  (* ---- the goal ---- *)
  clear Hloc Hs5 Hfrm Hspm HAm.
  exists FS.
  split; [exact HFSwm|].
  split; [exact HFS64|].
  split.
  { (* fp *)
    exists (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)), (Z_to_bv 64 RT_TSDMAIN), Cw, (Z_to_bv 64 T0), DBw, 0.
    split; [exact HTLS|].
    split; [rewrite EFS, MState.Z_to_bv_bv_unsigned; exact HFSb|].
    split.
    { unfold fs_place. split; [lia|]. split; [exact HFSalign|].
      split; [unfold ASAN_GT, RT_GT in *; lia|].
      split; [intros a Ha; apply HFSapp; unfold FS_SIZE, RT_FS_SIZE in *; lia|].
      split; [lia|]. split; [unfold FS_SIZE in *; lia|].
      intros a Ha. destruct (HFSpres a ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)) as (Hw & b & Hb).
      split; [exact Hw | exists b; exact Hb]. }
    split; [exact (word_mem_le8 rsegs mem (FS + 88) 20 HFS88 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [apply f6_byte_at; [lia | lia | exact HFS96]|].
    split.
    { apply Forall_cons; [|apply Forall_nil].
      unfold fp_cls. split; [lia|].
      destruct (f6_word_present mem (FS + 8) ltac:(lia) ltac:(lia)
          ltac:(intros i Hi;
                destruct (HFSpres (FS + 8 + i) ltac:(unfold AC.FS_SIZE in *; lia)) as (_ & bb & Hbb);
                exists bb; exact Hbb)) as (h & Hh).
      destruct (f6_bytes_P (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) mem (FS + 20480) 8192
          ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(intros i Hi;
                pose proof (HFSflag 1%nat i ltac:(lia) ltac:(change (AC.a_fs_M 1%nat) with 8192; lia)) as Hf;
                rewrite f6_afs_flag1 in Hf;
                destruct Hf as [Hf|Hf]; [exists (Z_to_bv 8 0) | exists (Z_to_bv 8 1)];
                  (split; [exact Hf | first [left; reflexivity | right; reflexivity]])))
                as (flags & Hfl & Hfllen & Hflb).
      exists h, flags.
      rewrite f6_fsh1, f6_fsf1, f6_fsM1.
      split; [exact Hh|]. split; [exact Hfl|]. split; [exact Hfllen | exact Hflb]. }
    split; [f6_num|].
    split; [intros a Ha; unfold app_mem; right; f6_num|].
    split.
    { (* the callee window is apart from the tls cells and the side stack's header *)
      change (reac_ctrl_parse_W 0 sp) with [(sp - REAC_CTRL_PARSE_K, sp)].
      rewrite f6_fs_frame0. unfold fp_dj.
      cbn [fp_tls app]. rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
      clear AS_C AS_T AS_DB DJ_C_FS DJ_T_FS DJ_DB_FS HFSalign.
      f6_dj_split; f6_num. }
    { (* the record block is apart from the class-1 side-stack bytes *)
      clear AS_C AS_T AS_DB DJ_C_FS DJ_T_FS DJ_DB_FS HFSalign.
      rewrite f6_fpw1.
      change (reac_ctrl_parse_D phi len 0) with ((if len <? 50 then [] else [(phi, phi + 50)]) ++ []).
      rewrite app_nil_r.
      destruct (len <? 50) eqn:EL.
      - unfold fp_dj. apply Forall_nil.
      - apply Z.ltb_ge in EL.
        assert (AS_PHI : RcLay.ly_dj phi (phi + 50) LOWMEM_END HIGHMEM_BEG).
        { apply (f6_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
          | intros x Hx; exact (proj1 (HPHI EL x Hx)) | exact HGAP]. }
        assert (DJ_PHI_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) phi (phi + 50)).
        { apply (f6_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
            [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
          intros x Hx. exact (proj2 (HPHI EL x Hx)). }
        unfold fp_dj. f6_dj_split; f6_num. } }
  { (* the tls clause: any witnesses are the ones above *)
    intros DT' TS' C' T' DB' k' HT'.
    assert (HOUT : Forall (fun d => forall x, fst d <= x < snd d -> outside (@nil ivl) x)
                     (fp_tls (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                        (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0)).
    { apply Forall_forall. intros d _ x _. exact I. }
    destruct (fl_tls_same mem mem [] (AC.as_tp AC.ASYMS)
                (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0
                DT' TS' C' T' DB' k' HTLS HT' (munch_refl (@nil ivl) mem) HOUT)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT' TS' C' T' DB' k'.
    rewrite f6_fpw1. unfold fp_dj. cbn [fp_tls app].
    rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
    clear HFSalign.
    f6_dj_split; f6_num. }
Qed.

(* The parse writes f6_PW S FS against the addresses a cut speaks of (S the caller's sp, FS the FakeStack base):
   every byte at or above S (the spill area, the saved registers, the stack above the entry sp) and the shadow
   of the app bytes there; the image below GT and its shadow; the frame and its shadow (fra_frame keeps it apart
   from the window, FRA's metadata bound from the class-1 frames); every app byte below stklo outside the
   FakeStack (the heap blocks) and its shadow; and the slot window below the callee's window and its shadow. *)
Lemma f6_PW_outs : forall g fr hb regs mem md S FS,
  FRA B APIf ra g fr hb regs mem md -> AC.aspZ regs = S ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall x, S <= x -> outside (f6_PW S FS) x) /\
  (forall x, S <= x < APPMEM_END -> outside (f6_PW S FS) (shadow_addr x)) /\
  (forall x, 0 <= x < AC.GT -> outside (f6_PW S FS) x /\ outside (f6_PW S FS) (shadow_addr x)) /\
  (forall x, fr <= x < fr + FRAME_BYTES -> outside (f6_PW S FS) x /\ outside (f6_PW S FS) (shadow_addr x)) /\
  (forall x, app_mem x -> x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (FS <= x < FS + AC.FS_SIZE) -> outside (f6_PW S FS) x /\ outside (f6_PW S FS) (shadow_addr x)) /\
  (forall x, g_S g - AF.SLOT_STACK <= x < S - REAC_CTRL_PARSE_K ->
     outside (f6_PW S FS) x /\ outside (f6_PW S FS) (shadow_addr x)).
Proof.
  intros g fr hb regs mem md S FS HFRA HS Htp HFS. pose proof FRAME_BYTES_val as HFBv.
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hapart & _ & HFSfr & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  rewrite Haspz in HS. subst S.
  rewrite Haspz in Hapart.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhigh.
  destruct (f6_fs_place _ _ _ FS HAH Htp HFS) as (HFSgt & HFSst & HFSm & HFSapp).
  pose proof (HFSfr FS Htp HFS) as HFSfr'.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (HKf : FS_SIZE = 11571200) by reflexivity.
  assert (HKF : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HKg : AC.GT = 6283264) by reflexivity.
  assert (HKn : FN_STACK = 1044480) by reflexivity.
  pose proof (Hapart REAC_CTRL_PARSE_K ltac:(lia)) as Hfrw.
  assert (HspH : HIGHMEM_BEG + 1044480 <= sp) by lia.
  assert (HSK : REAC_CTRL_PARSE_K <= sp) by lia.
  assert (HS8 : sp mod 8 = 0) by (clear - Hspm; Z.div_mod_to_equations; lia).
  assert (HFS8 : FS mod 8 = 0) by (clear - HFSm; Z.div_mod_to_equations; lia).
  assert (HWapp : forall a, sp - REAC_CTRL_PARSE_K <= a < sp -> app_mem a)
    by (intros a Ha; unfold app_mem; right; lia).
  assert (HFSapp' : forall a, FS <= a < FS + FS_SIZE -> app_mem a) by (intros a Ha; apply HFSapp; lia).
  assert (Osh1 : forall x, app_mem x -> (x + 1 <= sp - REAC_CTRL_PARSE_K \/ sp <= x) ->
            (x + 1 <= FS + 1085440 \/ FS + 2134016 <= x) -> outside (f6_PW sp FS) (shadow_addr x)).
  { intros x Hx H1 H2.
    pose proof (f6_sh_out sp FS x 1 0 HFSapp' HWapp HSK HS8 HFS8 ltac:(lia)
                  ltac:(rewrite Z.add_0_r; exact Hx) H1 H2) as Ho.
    rewrite Z.add_0_r in Ho. exact Ho. }
  split.
  { intros x Hx. rewrite f6_PW_eq. cbn [outside].
    assert (Q1 : (FS + 2134016) / 8 <= sp / 8) by (apply Z.div_le_mono; lia).
    assert (Q4 : sp / 8 + ASAN_K <= sp) by (rewrite HKk; clear - HspH HKh; Z.div_mod_to_equations; lia).
    repeat split; try exact I; intros HC; lia. }
  split.
  { intros x Hx. apply Osh1; [unfold app_mem; right; lia | right; lia | right; lia]. }
  split.
  { intros x Hx. split.
    - apply (f6_out_PW sp FS x HFSapp' HWapp HSK); [unfold app_mem; left; lia | lia | lia | lia | lia].
    - apply Osh1; [unfold app_mem; left; lia | left; lia | left; lia]. }
  split.
  { intros x Hx. split.
    - apply (f6_out_PW sp FS x HFSapp' HWapp HSK (Happ x Hx)); lia.
    - apply Osh1; [exact (Happ x Hx) | lia | lia]. }
  split.
  { intros x Hx Hlt Hnf. split.
    - apply (f6_out_PW sp FS x HFSapp' HWapp HSK Hx); lia.
    - apply Osh1; [exact Hx | left; lia | lia]. }
  { intros x Hx. split.
    - apply (f6_out_PW sp FS x HFSapp' HWapp HSK); [unfold app_mem; right; lia | lia | lia | lia | lia].
    - apply Osh1; [unfold app_mem; right; lia | left; lia | right; lia]. }
Qed.

(* sl_fr_cl (Tac_slot) for a run whose writes may include shadow bytes: RT by RT_meta_write (every shadow byte
   readable after the run), the registered globals and the slot window addressable by the caller (their shadow
   bytes are kept or rewritten by the callee's own post); the rest as sl_fr_cl. *)
Lemma f6_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 16 <= x < A + 312 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> outside W x) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HSH HAH' HSTK HWlo HWhdr HWA HWsaved HWsh
    HWwin HrecK HAG' HWA' E2 E3 E4 E8 E9 E19 E26.
  pose proof f6_ff as (SEGS & Hhead & Hlock & Hthr).
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWAo & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HSH)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split; [|exact (HrecK Hrec)].
        intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. exact (HWsh x ltac:(lia)). }
  split; [exact HWwin|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* FRA and ENT across the parse call (its post's munch over f6_PW: the window, the class-1 side-stack ranges, their
   shadow and the window's shadow) and across the lazy-page step md -> md'. AH / stklo / stkhi / ownership by
   a_laws_fs_store (every write outside a_store_ok is in the FakeStack or its shadow; a_fs_ok at return is
   f6_fs_ok_post); RT by RT_meta_write; the rest by f6_run, with every cell FRA reads outside f6_PW by f6_PW_outs,
   the S-anchored window and the window's addressability from the callee's post. ENT by ent_munch (no address ENT
   speaks of is written) and ent_mat. *)
Lemma f6_fra_call : forall g fr hb regs regs' mem mem' md md' S FS Wx Dx,
  FRA B APIf ra g fr hb regs mem md -> AC.aspZ regs = S ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  munch (f6_PW S FS) mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> shadow_rw mem' ->
  stk rsegs mem' (S - REAC_CTRL_PARSE_K) S ->
  addressable mem' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS (S - REAC_CTRL_PARSE_K) S Wx Dx ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ (ENT APIf g hb mem md -> ENT APIf g hb mem' md').
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md md' S FS Wx Dx HFRA HS Htp HFS MU WM HRO HSW Hstkw HADw HFP
    E2 E3 E4 E8 E9 E19 E26 Hmat.
  destruct (f6_PW_outs g fr hb regs mem md S FS HFRA HS Htp HFS) as (Ohi & Ohis & Olo & Ofr & Oblk & Owin).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  rewrite Haspz in HS. subst S.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhigh.
  destruct (f6_fs_place _ _ _ FS HAH Htp HFS) as (HFSgt & HFSst & HFSm & HFSapp).
  pose proof (proj1 (f6_fs_state _ _ _ FS HAH Htp HFS)) as Hok.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (HKf : FS_SIZE = 11571200) by reflexivity.
  assert (HKF : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HKg : AC.GT = 6283264) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HspH : HIGHMEM_BEG + 1044480 <= sp) by lia.
  assert (HSK : REAC_CTRL_PARSE_K <= sp) by lia.
  assert (HS8 : sp mod 8 = 0) by (clear - Hspm; Z.div_mod_to_equations; lia).
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HWapp : forall a, sp - REAC_CTRL_PARSE_K <= a < sp -> app_mem a)
    by (intros a Ha; unfold app_mem; right; lia).
  assert (HFSapp' : forall a, FS <= a < FS + FS_SIZE -> app_mem a) by (intros a Ha; apply HFSapp; lia).
  (* the stores agree with mem off a_store_ok, the FakeStack and its shadow *)
  assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by lia.
    rewrite f6_PW_eq. cbn [outside].
    split.
    { intros HC. apply Hns. unfold AC.a_store_ok. right; left. lia. }
    split; [intros HC; apply Hnfs; lia|].
    split; [intros HC; apply Hnfs; lia|].
    split; [intros HC; apply Hnfs; lia|].
    split.
    { intros HC. apply Hnsh. exists (8 * (a - ASAN_K)). split.
      - clear - HC HKk HKF. Z.div_mod_to_equations. lia.
      - unfold shadow_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    split; [|exact I].
    intros HC. apply Hns. unfold AC.a_store_ok. right; right; right. exists (8 * (a - ASAN_K)). split.
    - unfold shadow_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - right; left. clear - HC Hstklo HS4 HS8 Hspa HAS HAPP HKk HKs HKa. Z.div_mod_to_equations. lia. }
  assert (Hokp : AC.a_fs_ok mem' FS)
    by exact (f6_fs_ok_post mem mem' sp FS (AC.as_tp AC.ASYMS) Wx Dx Hok MU HFP HSK).
  assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a _ Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (f6_fs_store (hb ++ g_H g) mem mem' md FS HAH Htp HFS Hagree Hwm Hokp)
    as (HAH' & Hown & HSTKeq & HSTKhi).
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (f6_run g fr hb regs regs' mem mem' md (f6_PW sp FS) HFRA MU WM HRO).
    - (* rt_disjoint *)
      rewrite f6_PW_eq. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      assert (D1 : 0 <= (FS + 1085440) / 8) by (apply Z.div_pos; lia).
      assert (D2 : 0 <= (sp - 8800) / 8) by (apply Z.div_pos; lia).
      cbn [disjoint_from]. repeat split; first [exact I | left; lia].
    - intros a Ha. destruct (HSW a Ha) as (_ & b & Hb). exists b. exact Hb.
    - exact HAH'.
    - exact HSTKeq.
    - intros x Hx. exact (proj1 (Olo x ltac:(lia))).
    - intros x Hx. exact (proj1 (Ofr x ltac:(lia))).
    - intros A' HA' HA'r x Hx.
      assert (EA : A' = A) by (apply f6_id; [exact HA'r | exact HA64 | unfold rg in Hr9; rewrite <- HA'; exact Hr9]).
      subst A'. apply Ohi. lia.
    - intros x Hx. apply Ohi. lia.
    - intros x Hx.
      replace x with (shadow_addr (fr + 8 * (x - Sfr fr)))
        by (unfold Sfr, shadow_addr in *; clear - Hfr8; Z.div_mod_to_equations; lia).
      exact (proj2 (Ofr (fr + 8 * (x - Sfr fr)) ltac:(lia))).
    - (* the entry-anchored window after the call *)
      apply (fl_stk (f6_PW sp FS) mem mem' (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU WM).
      intros x Hx.
      destruct (Z_lt_le_dec x (sp - REAC_CTRL_PARSE_K)) as [Hl|Hl].
      + left. exact (proj1 (Owin x ltac:(lia))).
      + destruct (Z_lt_le_dec x sp) as [Hl2|Hl2].
        * right. destruct Hstkw as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
        * left. apply Ohi. exact Hl2.
    - (* the FakeStack frame record: its flag byte and slot word are class-6 cells, its tp word in the image *)
      intros (FS' & jj & Htp' & HFS'r & Hj & Hfrj & Hflag & Htail).
      assert (EFS : FS' = FS).
      { pose proof (f6_word_mem_eq mem _ _ _ Htp' Htp) as Hm. rewrite !Z.mod_small in Hm by lia. exact Hm. }
      subst FS'.
      assert (HB6 : fs_B 6 = 4096) by reflexivity.
      assert (HM6 : fs_M 6 = 256) by reflexivity.
      assert (Hfl : fs_flag FS 6 jj = FS + 36352 + jj) by (unfold fs_flag; cbn; lia).
      assert (Hfrv : fr = FS + 6328320 + jj * 4096) by (rewrite Hfrj; unfold fs_frame, fs_B; cbn; lia).
      rewrite HM6 in Hj.
      exists FS, jj.
      split.
      { apply (kb_word_munch rsegs mem mem' (f6_PW sp FS) _ FS Htp MU).
        intros k Hk. split; [unfold AC.as_tp, AC.ASYMS; cbn; lia|].
        apply (proj1 (Olo (AC.as_tp AC.ASYMS + k) ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia))). }
      split; [exact HFS|].
      split; [rewrite HM6; exact Hj|].
      split; [exact Hfrj|].
      split.
      { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx.
        apply (f6_out_PW sp FS x HFSapp' HWapp HSK); [apply HFSapp'; lia | lia | lia | lia | lia]. }
      { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx.
        rewrite HB6 in Hx.
        apply (f6_out_PW sp FS x HFSapp' HWapp HSK); [apply HFSapp'; lia | lia | lia | lia | lia]. }
    - (* the registered globals stay addressable: their shadow bytes are not written *)
      intros a Ha. pose proof (f6_ag_lt a Ha) as Hab.
      apply (addr1_munch (f6_PW sp FS) mem mem' a MU); [|exact (HAG a Ha)].
      exact (proj2 (Olo a Hab)).
    - (* the slot window outside the frame stays addressable *)
      intros a Ha Hnf.
      destruct (Z_le_gt_dec (sp - REAC_CTRL_PARSE_K) a) as [Hw1|Hw1];
        [destruct (Z_lt_ge_dec a sp) as [Hw2|Hw2]|].
      + exact (f6_addr1 mem' (sp - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K a HADw ltac:(lia)).
      + apply (addr1_munch (f6_PW sp FS) mem mem' a MU); [|exact (HWA a Ha Hnf)].
        exact (Ohis a ltac:(lia)).
      + apply (addr1_munch (f6_PW sp FS) mem mem' a MU); [|exact (HWA a Ha Hnf)].
        exact (proj2 (Owin a ltac:(lia))).
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split.
  { apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat. }
  intros HENT.
  eapply ent_mat; [|exact Hmat].
  eapply ent_munch with (W := f6_PW sp FS); [exact HENT | exact HAH | exact MU | | exact HSTKeq | exact HSTKhi |].
  - (* the entry blocks the target does not keep: app memory below stklo, off the side stack (f6_blocks) *)
    assert (Oent : forall q k i, In (q, k) (g_H g) -> 0 <= i < k ->
              outside (f6_PW sp FS) (q + i) /\ outside (f6_PW sp FS) (shadow_addr (q + i))).
    { intros q k i Hin Hi.
      destruct (f6_blocks (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (Hq4 & Hend & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
      exact (Oblk (q + i) Happq ltac:(lia)
               ltac:(intro HC; apply Hnfs; exists FS; split; [exact HFS | split; [exact Htp | exact HC]])). }
    intros x Hk. destruct Hk as [Hblk | [Himg | [Habv | [(b & Hor & ->) | Hblks]]]].
    + destruct Hblk as (q & k & i & Hin & _ & Hi & ->). exact (proj1 (Oent q k i Hin Hi)).
    + pose proof (img_below_GT x Himg) as Hxg. exact (proj1 (Olo x Hxg)).
    + exact (Ohi x ltac:(lia)).
    + destruct Hor as [Hi|Hr].
      * pose proof (img_below_GT b Hi) as Hbg. exact (proj2 (Olo b Hbg)).
      * exact (Ohis b ltac:(lia)).
    + destruct Hblks as (q & k & i & Hin & _ & Hi & ->). exact (proj2 (Oent q k i Hin Hi)).
  - intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* Everything the span's cut skeleton carries, across a write W that misses the cells it names: FLSI's spills
   (offsets 32 .. 272) and the ten b5_SPILL / two FSj words, all in [A + 32, A + 280), the frame body and
   the shadow of its bytes (out[]'s six bytes, the 17 identity bytes at fr + 2691, the fragment scratch, the
   identity record), the record block and the harness block (f1_IN) and their shadow, and the image below GT and
   its shadow (the kind-name table and the thread pointer words). *)
Lemma f6_keep : forall g j phi fr A regs regs' mem mem' md W,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  HB mem phi (flen g j) -> FLSI g j fr regs mem -> LK g fr j regs mem ->
  b5_C g j phi fr regs mem ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall x, A + 32 <= x < A + 280 -> outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x /\ outside W (shadow_addr x)) ->
  (forall x, phi <= x < phi + AC.a_size (flen g j) -> outside W x /\ outside W (shadow_addr x)) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  (forall x, 0 <= x < AC.GT -> outside W x /\ outside W (shadow_addr x)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 21 = getr regs 21 -> getr regs' 23 = getr regs 23 ->
  HB mem' phi (flen g j) /\ FLSI g j fr regs' mem' /\ LK g fr j regs' mem' /\
  b5_C g j phi fr regs' mem'.
Proof.
  intros g j phi fr A regs regs' mem mem' md W HFRA HHB HFLSI HLK HC H9 HA MU WM Osp Ofr Oph Oin Oim
    E2 E9 E18 E21 E23.
  pose proof HFRA as HF. pose proof FRAME_BYTES_val as HFBv.
  destruct HF as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by reflexivity.
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = A0).
  { apply f6_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  assert (Htp1 : 0 <= AC.as_tp AC.ASYMS /\ AC.as_tp AC.ASYMS + 16 <= AC.GT)
    by (unfold AC.as_tp, AC.ASYMS, AC.GT; cbn; lia).
  (* the kind-name table lies in the image below GT (v1.8 0x9e6a0, v1.9 0x9e760); its value is not needed *)
  assert (Hkn : 0 <= KIND_NAME /\ KIND_NAME + 4096 <= AC.GT) by (unfold KIND_NAME, AC.GT; lia).
  assert (Hknl : (length kind_name_bytes <= 4096)%nat) by (vm_compute; lia).
  pose proof HC as HC0.
  destruct HC0 as (Hs23 & Hs18 & (A1 & H9a & HA1 & HSP & Hq232) & HPH & HFR & HFS & HKN & HFG & HFSj).
  assert (HA1A : A1 = A).
  { apply f6_id; [lia | lia |]. unfold rg in H9, H9a. rewrite <- H9a. exact H9. }
  subst A1.
  assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite E9; exact H9).
  (* HB *)
  assert (HHB' : HB mem' phi (flen g j)).
  { destruct HHB as (Hnz & Had). split; [exact Hnz|].
    apply (f6_addr_keep W mem mem' phi (AC.a_size (flen g j)) Had MU).
    intros i Hi. exact (proj2 (Oph (phi + i) ltac:(lia))). }
  split; [exact HHB'|].
  (* FLSI = FLSH (PRO plus the loop part) and the four FLSI facts *)
  destruct HFLSI as (((Hf40 & Hf120 & Hf136 & Hf160 & Hf168 & Hf176 & Hf208 & Hf248p & Hfout6 &
                       Hinb & Hinblk & Hp184 & Hp256 & Hp264 & Hp272 & Hp32) &
                      Hf128 & Hfstk & Hf144 & Hfad17) &
                     Hf216 & Hf224 & Hf248 & (HIN1 & HINa & HINb) &
                     (Hc256 & Hc184 & Hc192 & Hc80 & Hc88 & Hc96 & Hc272 & Hc264 & HcAd72 & HcAd38 &
                      Hc72 & Hc64 & Hc56 & Hc48)).
  assert (Hsk : forall off v, 32 <= off <= 272 -> spill regs mem off v -> spill regs' mem' off v).
  { intros off v Hoff Hs.
    exact (f6_spill_keep regs regs' A off v mem mem' W Hs H9 HA ltac:(lia) ltac:(lia) E9 MU
             ltac:(intros x Hx; apply Osp; lia)). }
  split.
  { split.
    { split.
      { split; [exact (Hsk 40 _ ltac:(lia) Hf40)|].
        split; [exact (Hsk 120 _ ltac:(lia) Hf120)|].
        split; [exact (Hsk 136 _ ltac:(lia) Hf136)|].
        split; [exact (Hsk 160 _ ltac:(lia) Hf160)|].
        split; [exact (Hsk 168 _ ltac:(lia) Hf168)|].
        split; [exact (Hsk 176 _ ltac:(lia) Hf176)|].
        split; [exact (Hsk 208 _ ltac:(lia) Hf208)|].
        split; [exact (Hsk 248 _ ltac:(lia) Hf248p)|].
        split.
        { apply (f6_addr_keep W mem mem' (fr + 2624) 6 Hfout6 MU).
          intros i Hi. exact (proj2 (Ofr (fr + 2624 + i) ltac:(lia))). }
        split.
        { apply (fl_bytes W mem mem' (g_p g) (g_in g) Hinb MU).
          intros x Hx. rewrite <- g_n_len in Hx. exact (proj1 (Oin x Hx)). }
        split.
        { intros Hn. destruct (Hinblk Hn) as (Hin & Had). split; [exact Hin|].
          apply (f6_addr_keep W mem mem' (g_p g) (g_n g) Had MU).
          intros i Hi. exact (proj2 (Oin (g_p g + i) ltac:(lia))). }
        (* push 14 group D: A4's four frame pointers that PRO appends; v1.9: A4's [A+32] = fr + 2880 (`first`) *)
        split; [exact (Hsk 184 _ ltac:(lia) Hp184)|].
        split; [exact (Hsk 256 _ ltac:(lia) Hp256)|].
        split; [exact (Hsk 264 _ ltac:(lia) Hp264)|].
        split; [exact (Hsk 272 _ ltac:(lia) Hp272) | exact (Hsk 32 _ ltac:(lia) Hp32)]. }
      split; [exact (Hsk 128 _ ltac:(lia) Hf128)|].
      split.
      { apply (fl_stk W mem mem' fr (fr + FRAME_BYTES) Hfstk MU WM).
        intros x Hx. left. exact (proj1 (Ofr x Hx)). }
      split; [exact (Hsk 144 _ ltac:(lia) Hf144)|].
      apply (f6_addr_keep W mem mem' (fr + 2691) 17 Hfad17 MU).
      intros i Hi. exact (proj2 (Ofr (fr + 2691 + i) ltac:(lia))). }
    split; [exact (Hsk 216 _ ltac:(lia) Hf216)|].
    split; [exact (Hsk 224 _ ltac:(lia) Hf224)|].
    split; [exact (Hsk 248 _ ltac:(lia) Hf248)|].
    (* f1_IN: the harness block *)
    split.
    { split; [exact HIN1|].
      split.
      { apply (f6_addr_keep W mem mem' (g_p g) (g_n g) HINa MU).
        intros i Hi. exact (proj2 (Oin (g_p g + i) ltac:(lia))). }
      apply (fl_bytes W mem mem' (g_p g) (g_in g) HINb MU).
      intros x Hx. rewrite <- g_n_len in Hx. exact (proj1 (Oin x Hx)). }
    (* FLC (push 14 groups D / E) *)
    split; [exact (Hsk 256 _ ltac:(lia) Hc256)|].
    split; [exact (Hsk 184 _ ltac:(lia) Hc184)|].
    split; [exact (Hsk 192 _ ltac:(lia) Hc192)|].
    split; [exact (Hsk 80 _ ltac:(lia) Hc80)|].
    split; [exact (Hsk 88 _ ltac:(lia) Hc88)|].
    split; [exact (Hsk 96 _ ltac:(lia) Hc96)|].
    split; [exact (Hsk 272 _ ltac:(lia) Hc272)|].
    split; [exact (Hsk 264 _ ltac:(lia) Hc264)|].
    split.
    { apply (f6_addr_keep W mem mem' (fragb fr) 72 HcAd72 MU).
      intros i Hi. unfold fragb. exact (proj2 (Ofr (fr + 2768 + i) ltac:(lia))). }
    split.
    { apply (f6_addr_keep W mem mem' (fr + 2688) 38 HcAd38 MU).
      intros i Hi. exact (proj2 (Ofr (fr + 2688 + i) ltac:(lia))). }
    split; [exact (Hsk 72 _ ltac:(lia) Hc72)|].
    split; [exact (Hsk 64 _ ltac:(lia) Hc64)|].
    split; [exact (Hsk 56 _ ltac:(lia) Hc56) | exact (Hsk 48 _ ltac:(lia) Hc48)]. }
  (* LK *)
  destruct HLK as (Hj255 & H21 & HOURb).
  split.
  { split; [exact Hj255|]. split; [unfold rg in *; rewrite E21; exact H21|].
    unfold OURb in *. apply (fl_bytes W mem mem' (fr + 2624) (OUR (g_in g)) HOURb MU).
    rewrite OUR_length. intros x Hx. exact (proj1 (Ofr x ltac:(lia))). }
  (* b5_C *)
  split; [unfold rg in *; rewrite E23; exact Hs23|].
  split; [unfold rg in *; rewrite E18; exact Hs18|].
  split.
  { exists A. split; [exact H9'|]. split; [exact HA|].
    destruct HSP as (Hq248 & Hq256 & Hq144 & Hq184 & Hq192 & Hq80 & Hq88 & Hq96 & Hq272 & Hq264).
    split.
    { split; [exact (f6_q64_keep W mem mem' _ _ Hq248 MU ltac:(intros x Hx; apply Osp; lia))|].
      split; [exact (f6_q64_keep W mem mem' _ _ Hq256 MU ltac:(intros x Hx; apply Osp; lia))|].
      split; [exact (f6_q64_keep W mem mem' _ _ Hq144 MU ltac:(intros x Hx; apply Osp; lia))|].
      split; [exact (f6_q64_keep W mem mem' _ _ Hq184 MU ltac:(intros x Hx; apply Osp; lia))|].
      split; [exact (f6_q64_keep W mem mem' _ _ Hq192 MU ltac:(intros x Hx; apply Osp; lia))|].
      split; [exact (f6_q64_keep W mem mem' _ _ Hq80 MU ltac:(intros x Hx; apply Osp; lia))|].
      split; [exact (f6_q64_keep W mem mem' _ _ Hq88 MU ltac:(intros x Hx; apply Osp; lia))|].
      split; [exact (f6_q64_keep W mem mem' _ _ Hq96 MU ltac:(intros x Hx; apply Osp; lia))|].
      split; [exact (f6_q64_keep W mem mem' _ _ Hq272 MU ltac:(intros x Hx; apply Osp; lia))|].
      exact (f6_q64_keep W mem mem' _ _ Hq264 MU ltac:(intros x Hx; apply Osp; lia)). }
    (* push 13 group C: [A + 232] = the length flag *)
    exact (f6_q64_keep W mem mem' _ _ Hq232 MU ltac:(intros x Hx; apply Osp; lia)). }
  destruct HPH as (HPHb & HPHp & HPHfs).
  split.
  { split.
    { intros Hlen. pose proof (HPHb Hlen) as Hbs.
      apply (fl_bytes W mem mem' phi (t_g (g_in g) j) Hbs MU).
      rewrite f6_tg_len. intros x Hx. exact (proj1 (Oph x ltac:(unfold AC.a_size; lia))). }
    split.
    { intros Hlen. replace (AC.aspZ regs') with (AC.aspZ regs);
        [exact (HPHp Hlen) | unfold AC.aspZ; rewrite E2; reflexivity]. }
    { intros Hlen0 (b & Hb & Hw & Hr). apply (HPHfs Hlen0). exists b. split; [exact Hb|]. split; [|exact Hr].
      apply (proj2 (f6_word_eq W mem mem' (AC.as_tp AC.ASYMS) MU
                      ltac:(intros x Hx; exact (proj1 (Oim x ltac:(lia)))) ltac:(lia) ltac:(lia) b)).
      exact Hw. } }
  destruct HFR as (HFRa & HFRb & HFRc & HFRd).
  split.
  { split.
    { apply (f6_addr_keep W mem mem' (fragb fr) 72 HFRa MU).
      intros i Hi. unfold fragb. exact (proj2 (Ofr (fr + 2768 + i) ltac:(lia))). }
    split.
    { apply (f6_addr_keep W mem mem' (fr + 2688) 38 HFRb MU).
      intros i Hi. exact (proj2 (Ofr (fr + 2688 + i) ltac:(lia))). }
    split; [|exact HFRd].
    apply (fl_bytes W mem mem' (fragb fr) (t_FG (g_in g) j) HFRc MU).
    rewrite HFRd. unfold fragb. intros x Hx. exact (proj1 (Ofr x ltac:(lia))). }
  destruct HFS as (HFSa & DB & HDB & HDB0 & HDB1).
  split.
  { split.
    { intros FS0 Hw HFSr Hin. apply (HFSa FS0); [|exact HFSr|exact Hin].
      apply (proj2 (f6_word_eq W mem mem' (AC.as_tp AC.ASYMS) MU
                      ltac:(intros x Hx; exact (proj1 (Oim x ltac:(lia)))) ltac:(lia) ltac:(lia) FS0)).
      exact Hw. }
    exists DB. split; [|split; [exact HDB0 | exact HDB1]].
    apply (proj1 (f6_word_eq W mem mem' (AC.as_tp AC.ASYMS + 8) MU
                    ltac:(intros x Hx; exact (proj1 (Oim x ltac:(lia)))) ltac:(lia) ltac:(lia) DB)).
    exact HDB. }
  destruct HKN as (HKNa & HKNb).
  split.
  { split.
    { apply (fl_bytes W mem mem' KIND_NAME kind_name_bytes HKNa MU).
      intros x Hx. exact (proj1 (Oim x ltac:(lia))). }
    apply (f6_addr_keep W mem mem' KIND_NAME 112 HKNb MU).
    intros i Hi. exact (proj2 (Oim (KIND_NAME + i) ltac:(lia))). }
  (* FGj: the fragment record, the same 72 bytes at fragb fr = fr + 2768 as b5_FR's *)
  split.
  { destruct HFG as (HFGb & HFGok). split; [|exact HFGok].
    unfold FGBe in *. apply (fl_bytes W mem mem' (fr + 2768) (t_FG (g_in g) j) HFGb MU).
    rewrite HFRd. intros x Hx. exact (proj1 (Ofr x ltac:(lia))). }
  (* FSj, v1.9: [A+104] have, [A+112] n, and the body bytes at fr + 2880 (first.sroa.7) with their 35
     addressable bytes; the body is at most 23 bytes (f6_fs_body_len), inside the frame *)
  destruct HFSj as (Hs104 & Hs112 & Hbody & Hbad & HFI).
  split; [exact (Hsk 104 _ ltac:(lia) Hs104)|].
  split; [exact (Hsk 112 _ ltac:(lia) Hs112)|].
  split.
  { apply (fl_bytes W mem mem' (fr + 2880) _ Hbody MU).
    pose proof (f6_fs_body_len (g_in g) j) as HBL. intros x Hx. exact (proj1 (Ofr x ltac:(lia))). }
  split; [|exact HFI].
  apply (f6_addr_keep W mem mem' (fr + 2880) 35 Hbad MU).
  intros i Hi. exact (proj2 (Ofr (fr + 2880 + i) ltac:(lia))).
Qed.

(* f6_keep across the parse call: every cell it names is outside f6_PW (f6_PW_outs; the record block and the
   harness block are below stklo and, by a_laws_blocks, outside the FakeStack). *)
Lemma f6_call_keep : forall g j phi fr regs regs' mem mem' md S FS,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md -> AC.aspZ regs = S ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  HB mem phi (flen g j) -> FLSI g j fr regs mem -> LK g fr j regs mem -> b5_C g j phi fr regs mem ->
  munch (f6_PW S FS) mem mem' -> wmono rsegs mem mem' ->
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 21 = getr regs 21 -> getr regs' 23 = getr regs 23 ->
  HB mem' phi (flen g j) /\ FLSI g j fr regs' mem' /\ LK g fr j regs' mem' /\
  b5_C g j phi fr regs' mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g j phi fr regs regs' mem mem' md S FS HFRA HS Htp HFS HHB HFLSI HLK HC MU WM E2 E9 E18 E21 E23.
  destruct (f6_PW_outs g fr _ regs mem md S FS HFRA HS Htp HFS) as (Ohi & Ohis & Olo & Ofr & Oblk & Owin).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  destruct (f6_blocks (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi (AC.a_size (flen g j)) HAH
              ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hpstk & Hall).
  pose proof HFLSI as (_ & _ & _ & _ & (HIN1 & _ & _) & _).
  apply (f6_keep g j phi fr A regs regs' mem mem' md (f6_PW S FS) HFRA HHB HFLSI HLK HC Hr9 HA64 MU WM).
  - intros x Hx. apply Ohi. lia.
  - exact Ofr.
  - intros x Hx. destruct (Hall x Hx) as (Happx & Hnfs). apply (Oblk x Happx); [lia|].
    intro HC'. apply Hnfs. exists FS. split; [exact HFS | split; [exact Htp | exact HC']].
  - intros x Hx.
    destruct (f6_blocks (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md (g_p g) (g_n g) HAH
                (in_or_app _ _ _ (or_intror (HIN1 ltac:(lia))))) as (_ & Hist & Hiall).
    destruct (Hiall x Hx) as (Happx & Hnfs). apply (Oblk x Happx); [lia|].
    intro HC'. apply Hnfs. exists FS. split; [exact HFS | split; [exact Htp | exact HC']].
  - exact Olo.
  - exact E2.
  - exact E9.
  - exact E18.
  - exact E21.
  - exact E23.
Qed.

(* FRA and ENT move across the store [A+280, A+288) of 0x81f4c. The write is app memory above stklo
   (stklo <= S - SLOT_STACK < sp <= A) and below the entry sp S, so it is a_store_ok for a_laws_store; it misses
   every FRA cell: the frame header and the FRAME_SHADOW (392) frame shadow bytes (the frame is below A, the
   shadow below HIGHMEM_BEG <= A), the A+304 and A+16..A+32 words, the saved registers [S-104, S) and the low runtime and
   image cells. It lies inside the entry-anchored slot window [S - SLOT_STACK, S), so ent_store keeps ENT, and
   the FakeStack frame record lies below stklo, so fsrec_stklo keeps it. *)
Lemma f6_fra_spill : forall g fr hb regs regs' mem mem' md md' Asp,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  rg regs 9 Asp -> 0 <= Asp < 2 ^ 64 ->
  munch [(Asp + 280, Asp + 288)] mem mem' ->
  wmono rsegs mem mem' ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  AsanLift.mat_le md md' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md md' Asp HFRA HENT H9 HA MU WM HWIN' Hmat
    E2 E3 E4 E8 E9 E19 E26.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HAsr : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HspN : HIGHMEM_BEG < sp) by lia.
  assert (HA0e : Asp = A0).
  { apply f6_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  assert (HfrL : 0 <= fr).
  { pose proof (bytes_at_bound rsegs mem fr (le8 (Z_to_bv 64 0x41b58ab3)) Hhdr1) as (Hf0 & _). lia. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = Asp).
  { intros A' HA' HA'r. apply f6_id; [lia | lia |]. rewrite <- HA'. exact H9. }
  set (W := [(Asp + 280, Asp + 288)]) in MU.
  assert (HOUT : forall x, 0 <= x < HIGHMEM_BEG -> outside W x).
  { intros x Hx. subst W. cbn [outside]. repeat split; try exact I; lia. }
  assert (HRO : ro_agree rsegs mem').
  { apply (sl_ro_keep W mem mem' Hro MU). intros x Hx. exact (HOUT x ltac:(lia)). }
  assert (HAW : all_app W).
  { subst W. cbn [all_app]. split; [apply f6_app_ivl; lia | exact I]. }
  assert (HD : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN. cbn [disjoint_from]. repeat split; first [exact I | left; lia]. }
  assert (Hwrit : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hmc : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    subst W. cbn [outside]. repeat split; try exact I; intro HC; apply Hns;
      right; left; lia. }
  destruct (f6_store (hb ++ g_H g) mem mem' md HAH Hmc Hwrit) as (HAH' & Hown & HSTKeq & HSTKhi).
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_stk_run B APIf ra empty FF g fr hb regs regs' mem mem' md W
             HFRA MU WM HRO HAW HD HAH' HSTKeq).
    - (* frame header [fr, fr+24) *)
      intros x Hx. subst W. cbn [outside ULFr.outside]. repeat split; try exact I; lia.
    - (* everything below HIGHMEM_BEG *)
      intros x Hx. exact (HOUT x ltac:(lia)).
    - (* the frame-base spill [A+304, A+312) *)
      intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx.
      subst W. cbn [outside ULFr.outside]. repeat split; try exact I; lia.
    - (* the 13 saved caller registers [S-104, S) *)
      intros x Hx. subst W. cbn [outside ULFr.outside]. repeat split; try exact I; lia.
    - (* the FRAME_SHADOW frame shadow bytes *)
      intros x Hx. subst W. cbn [outside ULFr.outside]. repeat split; try exact I;
        revert Hx; unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia.
    - (* the fr reload and release-arm selector spills [A+24, A+40) *)
      intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx.
      subst W. cbn [outside ULFr.outside]. repeat split; try exact I; lia.
    - exact HWIN'.
    - (* the FakeStack frame record: its three cells are at or below stklo *)
      intros Hrec. eapply fsrec_stklo with (W := W); [exact Hrec | exact HAH | exact MU |].
      intros x Hx _. subst W. cbn [outside ULFr.outside]. repeat split; try exact I; lia.
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
  - eapply ent_mat; [| exact Hmat].
    eapply ent_store with (W := W); [exact HENT | exact HFRA | exact MU | | exact HSTKeq | exact HSTKhi |].
    + intros x Hx.
      destruct (Z_lt_le_dec x (Asp + 280)) as [H1|H1];
        [| destruct (Z_lt_le_dec x (Asp + 288)) as [H2|H2]].
      * left. subst W. cbn [outside ULFr.outside]. repeat split; try exact I; lia.
      * right. left. lia.
      * left. subst W. cbn [outside ULFr.outside]. repeat split; try exact I; lia.
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ---------------- the segment lemmas ---------------- *)

(* 0x81f54 -> 0x81f64: the three argument moves and the parse call, on the contract. *)
Lemma seg_F6_ebc : forall j,
  Hat B APIf ra (Inv_A81f64_at B APIf ra) j -> Hat B APIf ra (Inv_A81f54_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j Hexit g c HInv.
  pose proof (proj1 f6_ff) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & HK & HIDj & HF17 & HW240 & HPF)).
  subst c. rewrite SEGS.
  pose proof HK as HK0.
  destruct HK0 as (H20 & H22 & H24 & H25 & H280 & Hu32 & Hra).
  pose proof HC as HC0.
  destruct HC0 as (Hs7 & Hs2 & (A & H9 & HA & HSP & _) & HPH & HFR & HFS & HKN & _ & _).
  destruct HPH as (HPHb & HPHp & HPHfs).
  destruct (f6_fp_call g fr phi (flen g j) regs mem md HFRA HFS) as (FS & HTPw & HFS64 & HFP & HTLS).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (HKn : FN_STACK = 1044480) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = Asp).
  { apply f6_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A.
  destruct (fra_callee_fp B APIf ra g fr _ regs mem md REAC_CTRL_PARSE_K [1%nat] FS _ _ _ _ HFRA
              ltac:(lia) HFP HTLS ltac:(lia) ltac:(lia))
    as (HWhi & HWtop & HWm16 & HWstk & HWapp & HWaddr & _ & _).
  rewrite Haspz in HFP, HTLS, HWhi, HWtop, HWm16, HWstk, HWapp, HWaddr.
  destruct (f6_blocks (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi (AC.a_size (flen g j)) HAH
              ltac:(apply in_or_app; left; left; reflexivity)) as (Hp4096 & Hpstk & Hpall).
  pose proof (f6_flen_nn g j) as Hflen0.
  assert (Hphi : 0 <= phi /\ phi + Z.max (flen g j) 1 <= APPMEM_END).
  { destruct HHB as (_ & Had). destruct Had as (Hp0 & _ & Hpn & _). unfold AC.a_size in Hpn. lia. }
  assert (HTPu : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS)
    by (rewrite Hr4; apply MState.unsigned_lit; unfold AC.as_tp, AC.ASYMS; cbn; lia).
  destruct (f6_rt_cells sp mem md HRT) as (HB1 & HB2 & HB3 & HB4 & HB5).
  apply (sl_run_lib regs (Z_to_bv 64 0x81f54) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x81f64 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\
       getr R0 10 = Z_to_bv 64 (t_k (g_in g) j) /\
       munch (f6_PW sp FS) mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (sp - REAC_CTRL_PARSE_K) sp /\ shadow_rw mem' /\
       addressable mem' (sp - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
       fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS (sp - REAC_CTRL_PARSE_K) sp (reac_ctrl_parse_W 0 sp)
         (reac_ctrl_parse_D phi (flen g j) 0))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { rewrite f6_mkR_expand. rewrite Hr2. f6_slot Hs2. f6_slot Hs7.
      eapply f6_ebc_evt with (f := phi) (n := flen g j) (S := sp) (FS := FS) (bs := t_g (g_in g) j).
      - lia.
      - lia.
      - lia.
      - exact Hspm.
      - exact HWhi.
      - exact HWtop.
      - exact HWstk.
      - exact Hro.
      - exact (f6_tg_len (g_in g) j).
      - intros Hbig. unfold AC.a_size in *. split; [lia|]. split; [lia|]. left. lia.
      - intros i Hi. destruct (Z_lt_le_dec (flen g j) 50) as [Hlt|Hge].
        + rewrite (f6_cp_rd_short (flen g j) (t_g (g_in g) j) Hlt) in Hi. destruct Hi.
        + destruct (HPHb Hge) as (_ & _ & HB3'). pose proof (f6_cp_rd_lt _ _ i Hi) as Hilt.
          apply HB3'. rewrite (f6_tg_len (g_in g) j). exact Hilt.
      - exact (AsanRTInv.RT_cells sp mem md HRT).
      - exact (AsanRTInv.RT_shadow_rw sp mem md HRT).
      - exact HWaddr.
      - intros Hbig. rewrite <- (Z.add_0_r phi).
        apply (addressable_sub mem phi (AC.a_size (flen g j)) 0 50 (proj2 HHB)); unfold AC.a_size; lia.
      - exact (f6_bc_addr mem HAG).
      - exact HB1.
      - exact HB2.
      - exact HB3.
      - exact HB4.
      - exact HB5.
      - rewrite HTPu. exact HFP.
      - rewrite HTPu. exact HTLS. }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
        E & MU & WM & RO & ST & SR & AD & FPp).
      eexists _, (Z_to_bv 64 0x81f64), m'. split; [exact E|].
      split; [reflexivity|].
      split; [symmetry; exact Hr2|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [symmetry; exact Hs2|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [symmetry; exact Hs7|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact RO|]. split; [exact ST|].
      split; [exact SR|]. split; [exact AD|]. rewrite HTPu in FPp; exact FPp. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 & Er22 & Er23 &
      Er24 & Er25 & Er26 & Er10 & MU & WM & RO' & ST' & SR' & AD' & FPp) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (t_k (g_in g) j)) by (rewrite Hreg; exact Er10).
    destruct (f6_fra_call g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md md' sp FS _ _
                HFRA Haspz HTPw HFS64 MU WM RO' SR' ST' AD' FPp Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat)
      as (HFRA'' & HENTf).
    pose proof (HENTf HENT) as HENT''.
    destruct (f6_PW_outs g fr _ regs mem md sp FS HFRA Haspz HTPw HFS64)
      as (Ohi & _ & _ & Ofr & Oblk & _).
    destruct (f6_call_keep g j phi fr regs regs' mem mem' md sp FS HFRA Haspz HTPw HFS64 HHB
                HFLSI HLK HC MU WM Fr2 Fr9 Fr18 Fr21 Fr23)
      as (HHB' & HFLSI' & HLK' & HC').
    pose proof (f6_idj_keep g fr j _ mem mem' HIDj MU
                  ltac:(intros x Hx; exact (proj1 (Ofr x Hx)))) as HIDj'.
    (* the record block: app memory below stklo and, by a_laws_blocks, outside the FakeStack *)
    assert (Oph : forall x, phi <= x < phi + AC.a_size (flen g j) ->
              outside (f6_PW sp FS) x /\ outside (f6_PW sp FS) (shadow_addr x)).
    { intros x Hx. destruct (Hpall x Hx) as (Happx & Hnfs).
      apply (Oblk x Happx); [lia|].
      intro HCb. apply Hnfs. exists FS. split; [exact HFS64 | split; [exact HTPw | exact HCb]]. }
    assert (HphiB : 0 <= phi /\ phi + AC.a_size (flen g j) <= APPMEM_END)
      by (destruct HHB as (_ & (Hp0 & _ & Hpn & _)); lia).
    assert (Hqk : forall off v, 0 <= off <= 408 -> q64 mem (Asp + off) v -> q64 mem' (Asp + off) v).
    { intros off v Hoff Hqv.
      exact (f6_q64_keep _ mem mem' _ _ Hqv MU ltac:(intros x Hx; apply Ohi; lia)). }
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA''|].
    split; [exact HENT''|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split.
    { (* b5_K *)
      unfold b5_K.
    split; [unfold rg in *; rewrite Fr20; exact H20|].
    split; [unfold rg in *; rewrite Fr22; exact H22|].
    split; [unfold rg in *; rewrite Fr24; exact H24|].
    split; [unfold rg in *; rewrite Fr25; exact H25|].
    split.
    { destruct H280 as (A' & H9' & HA' & Hq).
      assert (EA : A' = Asp).
      { apply f6_id; [lia | lia |]. unfold rg in H9', Hr9. rewrite <- H9'. exact Hr9. }
      subst A'.
      exists Asp. split; [unfold rg in *; rewrite Fr9; exact Hr9|]. split; [exact HA'|].
      exact (f6_q64_keep _ mem mem' _ _ Hq MU ltac:(intros x Hx; apply Ohi; lia)). }
      split; [|exact Hra].
      unfold u32 in *. apply (fl_bytes _ mem mem' _ _ Hu32 MU).
      rewrite length_le4. intros x Hx. exact (proj1 (Ofr x ltac:(cbn [Z.of_nat] in Hx; lia))). }
    split; [unfold rg; exact Fr10|].
    split; [exact HIDj'|].
    (* push 13 group C: [A + 192], the guarded [A + 240] and the record group across the parse call *)
    split.
    { destruct HF17 as (A' & H9f & HAf & Hq192).
      rewrite (f6_id A' Asp HAf HAspR ltac:(unfold rg in H9f, Hr9; rewrite <- H9f; exact Hr9)) in Hq192.
      exists Asp. split; [unfold rg in *; rewrite Fr9; exact Hr9|]. split; [exact HAspR|].
      apply Hqk; [lia | exact Hq192]. }
    split.
    { destruct HW240 as (A' & H9w & HAw & (w240 & Hqw & Hwr & Hw1 & Hw0)).
      rewrite (f6_id A' Asp HAw HAspR ltac:(unfold rg in H9w, Hr9; rewrite <- H9w; exact Hr9)) in Hqw.
      exists Asp. split; [unfold rg in *; rewrite Fr9; exact Hr9|]. split; [exact HAspR|].
      exists w240. split; [apply Hqk; [lia | exact Hqw]|].
      split; [exact Hwr|]. split; [exact Hw1 | exact Hw0]. }
    exact (f6_pf_keep g j phi fr Asp regs regs' mem mem' (f6_PW sp FS) HPF Hr9 HAspR ltac:(lia) Fr9 MU
             (proj1 HphiB) (proj2 HphiB) ltac:(intros x Hx; apply Ohi; lia) Ofr Oph).
Qed.

(* 0x81ec0 -> 0x81f54: the byte-sum loop, the two byte checks, the abort compare NOT taken and the store
   [s1+280] = (the low byte of the sum = 0) = b2z (t_sum_ok j), with s4 = 1 - b2z (t_sum_ok j) and
   s9 = b2z (t_tfill j). *)
Lemma seg_F6_e28 : forall j,
  Hat B APIf ra (Inv_A81f54_at B APIf ra) j -> Hat B APIf ra (Inv_A81ec0_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j Hexit g c HInv.
  pose proof (proj1 f6_ff) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & Hlen50 & Ha0 & Ha1 & Ha2 & Ha3 & Hs6 & Hs8 & Hs9 & Hq240 & Hu32 &
     HIDj & HF17 & HW240 & HPF)).
  subst c. rewrite SEGS.
  pose proof HC as HC0.
  destruct HC0 as (Hs7 & Hs2 & (A & H9 & HA & HSP & _) & HPH & HFR & HFS & HKN & _ & _).
  pose proof (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hfr0 : 0 < fr) by (unfold AC.GT in HGT; lia).
  assert (HAeq : A = Asp).
  { apply f6_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A.
  destruct Hq240 as (A' & H9' & HA' & Hq240).
  assert (HA'eq : A' = Asp).
  { apply f6_id; [lia | lia |]. unfold rg in H9', Hr9. rewrite <- H9'. exact Hr9. }
  subst A'.
  destruct (f6_blocks (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi (AC.a_size (flen g j)) HAH
              ltac:(apply in_or_app; left; left; reflexivity)) as (Hp4096 & Hpstk & _).
  assert (Hbig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; exact Hlen50).
  pose proof HPH as HPH0.
  destruct HPH0 as (HPHb & _ & _).
  pose proof (HPHb Hlen50) as Hbs.
  assert (Haddr50 : addressable mem phi 50)
    by (rewrite <- (Z.add_0_r phi);
        apply (addressable_sub mem phi (AC.a_size (flen g j)) 0 50 (proj2 HHB)); unfold AC.a_size; lia).
  assert (Hphi : 0 <= phi /\ phi + 50 <= 2 ^ 64).
  { destruct Haddr50 as (Hp0 & _ & Hpn & _). lia. }
  pose proof (f6_spill_stk g fr (hb1 phi (AC.a_size (flen g j))) regs mem md Asp
                (Asp + 240) (Asp + 288) HFRA Hr9 HAspR ltac:(lia) ltac:(lia) ltac:(lia)) as HSTK240.
  assert (Htk : 0 <= t_k (g_in g) j < 2 ^ 64)
    by (pose proof (ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)); unfold t_k; lia).
  set (bsum := psum (skipn 18 (t_g (g_in g) j)) 32 mod 256).
  set (memW := write_to_mem mem (wa (Asp + 280)) (le8 (Z_to_bv 64 (if bsum =? 0 then 1 else 0)))).
  apply (sl_run_lib regs (Z_to_bv 64 0x81ec0) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x81f54 /\ mem' = memW /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\
       getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\ getr R0 26 = getr regs 26 /\
       getr R0 20 = Z_to_bv 64 (if bsum =? 0 then 0 else 1) /\
       getr R0 25 = Z_to_bv 64 (f6_s9 (t_g (g_in g) j)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { rewrite f6_mkR_expand.
      f6_slot Hr9. f6_slot Ha0. f6_slot Ha1. f6_slot Ha2. f6_slot Ha3.
      f6_slot Hs2. f6_slot Hs7. f6_slot Hs8. f6_slot Hr26.
      apply (f6_e28_evt (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 25) (getr regs 27)
               (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
               fp_regs fp_csr mem phi Asp (flen g j) (t_k (g_in g) j) (b2z (t_8819 (g_in g) j))
               (t_g (g_in g) j));
        [ lia | lia | exact (f6_tg_len (g_in g) j) | exact Hbs | exact Haddr50 | lia | lia
        | exact HSTK240 | exact Htk | exact Hq240 | ].
      rewrite <- (f6_8819_eq (g_in g) j). rewrite MState.unsigned_lit by lia. reflexivity. }
    { intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & E).
      eexists _, (Z_to_bv 64 0x81f54), _. split; [exact E|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [symmetry; exact Hr9|]. split; [symmetry; exact Hs2|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [symmetry; exact Hs7|]. split; [symmetry; exact Hs8|]. split; [symmetry; exact Hr26|].
      split; reflexivity. }
  - intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er21 & Er22 & Er23 &
      Er24 & Er26 & Er20 & Er25) Hreg Hmat.
    subst pc' mem'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr20 : getr regs' 20 = Z_to_bv 64 (if bsum =? 0 then 0 else 1)) by (rewrite Hreg; exact Er20).
    assert (Fr25 : getr regs' 25 = Z_to_bv 64 (f6_s9 (t_g (g_in g) j))) by (rewrite Hreg; exact Er25).
    set (W := [(Asp + 280, Asp + 288)]).
    assert (MU : munch W mem memW).
    { subst W memW. apply (munch_write _ mem mem (Asp + 280) (le8 (Z_to_bv 64 (if bsum =? 0 then 1 else 0))));
        [ apply munch_refl | lia | rewrite length_le8; lia
        | rewrite length_le8; cbn [inside]; left; lia ]. }
    assert (WM : wmono rsegs mem memW) by (subst memW; apply wmono_write; apply wmono_refl).
    assert (HWIN' : stk rsegs memW (g_S g - AF.SLOT_STACK) (g_S g)).
    { subst memW. apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]. }
    destruct (f6_fra_spill g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem memW md md' Asp
                HFRA HENT Hr9 HAspR MU WM HWIN' Hmat Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26) as (HFRA'' & HENT'').
    (* the carried skeleton: everything it names is below Asp + 280 *)
    assert (O1 : forall x, x <= APPMEM_END -> x < Asp + 280 -> outside W x /\ outside W (shadow_addr x)).
    { intros x Hx1 Hx2. pose proof (f6_sh_hi x Hx1) as Hsh'. subst W. cbn [outside].
      split; (split; [lia | exact I]). }
    (* the harness block (f1_IN): a live block, below stklo <= sp - FN_STACK, so below Asp + 280 *)
    assert (Oin : forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)).
    { intros x Hx. pose proof HFLSI as (_ & _ & _ & _ & (HIN1 & _ & _) & _).
      destruct (f6_blocks (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror (HIN1 ltac:(lia))))) as (_ & Hist & Hiall).
      pose proof (fra_win B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hwlo & _).
      pose proof (proj1 (Hiall x Hx)) as Happx. unfold app_mem in Happx.
      assert (HKn : FN_STACK = 1044480) by reflexivity.
      assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
      apply O1; lia. }
    destruct (f6_keep g j phi fr Asp regs regs' mem memW md W HFRA HHB HFLSI HLK HC Hr9 HAspR MU WM
                ltac:(intros x Hx; exact (proj1 (O1 x ltac:(lia) ltac:(lia))))
                ltac:(intros x Hx; exact (O1 x ltac:(lia) ltac:(lia)))
                ltac:(intros x Hx; exact (O1 x ltac:(lia) ltac:(lia)))
                Oin
                ltac:(intros x Hx; exact (O1 x ltac:(lia) ltac:(lia)))
                Fr2 Fr9 Fr18 Fr21 Fr23)
      as (HHB' & HFLSI' & HLK' & HC').
    pose proof (f6_idj_keep g fr j W mem memW HIDj MU
                  ltac:(intros x Hx; exact (proj1 (O1 x ltac:(lia) ltac:(lia))))) as HIDj'.
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', memW, md', fr.
    split; [reflexivity|].
    split; [exact HFRA''|].
    split; [exact HENT''|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split.
    { (* b5_K *)
    unfold b5_K.
    split.
    { unfold rg. rewrite Fr20, (f6_sum (g_in g) j Hbig). unfold bsum.
      destruct (psum (skipn 18 (t_g (g_in g) j)) 32 mod 256 =? 0); reflexivity. }
    split; [rewrite Hbig; unfold rg in *; rewrite Fr22; exact Hs6|].
    split; [unfold rg in *; rewrite Fr24; exact Hs8|].
    split; [rewrite (f6_tfill (g_in g) j Hbig); unfold rg; exact Fr25|].
    split.
    { exists Asp. split; [unfold rg in *; rewrite Fr9; exact Hr9|]. split; [exact HAspR|].
      rewrite (f6_sum (g_in g) j Hbig). subst memW. unfold q64, bsum.
      apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    split.
    { unfold u32 in *. apply (fl_bytes W mem memW _ _ Hu32 MU).
      rewrite length_le4. intros x Hx. exact (proj1 (O1 x ltac:(cbn [Z.of_nat] in Hx; lia)
                                                     ltac:(cbn [Z.of_nat] in Hx; lia))). }
      apply f6_reply; [exact (proj1 HHB) | exact Hfr0]. }
    split; [exact HIDj'|].
    (* push 13 group C: [A + 192] and the guarded [A + 240] across the [A + 280] store *)
    split.
    { destruct HF17 as (A' & H9f & HAf & Hq192).
      rewrite (f6_id A' Asp HAf HAspR ltac:(unfold rg in H9f, Hr9; rewrite <- H9f; exact Hr9)) in Hq192.
      exists Asp. split; [unfold rg in *; rewrite Fr9; exact Hr9|]. split; [exact HAspR|].
      exact (f6_q64_keep W mem memW _ _ Hq192 MU
               ltac:(intros x Hx; exact (proj1 (O1 x ltac:(lia) ltac:(lia))))). }
    split.
    { destruct HW240 as (A' & H9w & HAw & (w240 & Hqw & Hwr & Hw1 & Hw0)).
      rewrite (f6_id A' Asp HAw HAspR ltac:(unfold rg in H9w, Hr9; rewrite <- H9w; exact Hr9)) in Hqw.
      exists Asp. split; [unfold rg in *; rewrite Fr9; exact Hr9|]. split; [exact HAspR|].
      exists w240. split.
      { exact (f6_q64_keep W mem memW _ _ Hqw MU
                 ltac:(intros x Hx; exact (proj1 (O1 x ltac:(lia) ltac:(lia))))). }
      split; [exact Hwr|]. split; [exact Hw1 | exact Hw0]. }
    (* b5_PF: carried from the entry (push 14), across the [A + 280] store *)
    assert (HphiB : 0 <= phi /\ phi + AC.a_size (flen g j) <= APPMEM_END)
      by (destruct HHB as (_ & (Hp0 & _ & Hpn & _)); lia).
    exact (f6_pf_keep g j phi fr Asp regs regs' mem memW W HPF Hr9 HAspR ltac:(lia) Fr9 MU
             (proj1 HphiB) (proj2 HphiB)
             ltac:(intros x Hx; exact (proj1 (O1 x ltac:(lia) ltac:(lia))))
             ltac:(intros x Hx; exact (O1 x ltac:(lia) ltac:(lia)))
             ltac:(intros x Hx; exact (O1 x ltac:(lia) ltac:(lia)))).
Qed.

Lemma seg_F6 : forall j, Hat B APIf ra (Inv_A81f64_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81f54_at B APIf ra) j /\ Hat B APIf ra (Inv_A81ec0_at B APIf ra) j.
Proof.
  intros j Hexit. pose proof (seg_F6_ebc j Hexit) as Hebc.
  split; [exact Hebc | exact (seg_F6_e28 j Hebc)].
Qed.

End S.
