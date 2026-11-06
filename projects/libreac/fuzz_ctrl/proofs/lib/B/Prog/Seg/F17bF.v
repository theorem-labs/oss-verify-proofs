(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v, with its module paths, module names and addresses changed; 1175 of its 1288 lines of code are new or changed and 1596 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F17b.v, with its module paths, module names and numbers changed; 387 of its 471 lines of code are new or changed and 1204 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F17b.v f17_lu_evt (:76) and the inline stretch of seg_F17b (:706, stepped at
     :760-1049 and exited at :1204 / :1210) at a working branch 3803efccea0
     (blob dc9ae8087a72de90382bb6524f59281543b429f5);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: seg_F17b_pre_F re-runs F17b.v lines 782-1049 (the body from 0x82468 up to the `jal __asan_memcpy`
     at 0x82630) and lines 1195-1210 (the two guard exits), with the segment's own cut facts restated as
     premises over regs / mem / Z; f17_lu_evt_F re-derives F17b.v:76 from an evtF. *)
(* rule 24: no function proved. *)
(* Footprint twin of segment S_F17b's machine stretch 0x82468 -> {0x82634, __asan_memcpy}. It is the PRE-CALL
   stretch: it stops AT the callee entry (pc = ASAN_MEMCPY, ra = 0x82634, a0 = fr + 2885, a1 = Phi + 27,
   a2 = gg[26]) on the arm that opens the record, and at the F18 entry cut 0x82634 with memory unchanged on every
   arm that does not. There is no _post_F: the memcpy returns at 0x82634, which IS the exit cut, so the post
   stretch is empty (Tac_f17bF.v f17_post_F states that zero-step piece); the callee itself is composed by the
   walk, never re-stated here.
   Accesses (instruction fetch is not an access):
     read  [A + 248, A + 256)            ld a1,248(s1)        the length-and-sum guard flag
     read  [Phi + 16, Phi + 27)          9 x lbu              the record's tested bytes 16..19, 22..26
     read  the shadow bytes of Phi + 16 .. Phi + 26           the nine instrumented checks (lb of the metadata
                                                              byte at (X >> 3) + ASAN_K) and the re-check of
                                                              Phi + 26 after the first store
     read  [A + 312, A + 320)            3 x ld a?,312(s1)    the block spill (Phi + 18)
     read  [A + 168, A + 176)            2 x ld a?,168(s1)    the spill of `first` (fr + 2880)
     read  [A + 88, A + 96)              ld a0,88(s1)         the spill of the body of `first` (fr + 2885)
     write [fr + 2880, fr + 2885)        sw s6,0(a1); sb a2,4(a0)
   so seven rng premises. The shadow range is the unaligned form of the brief:
   [(Phi+16) >> 3 + ASAN_K, (Phi+26) >> 3 + ASAN_K]. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F17b Tac_f17b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Exec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* lib.Prog's RcFrag chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy; this
   file's registers, mkst and FPState must be image B's, as SlotInv's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module ACPY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpy_c.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module RM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module UEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.

(* ---- The F17b.v helpers the stepping needs, restated over the lib.Lib engine (F17b.v states them over the UL
   engine's value functions and read facts, which the StepF steps do not match). The proofs are its own. ---- *)

(* A carried byte range, in the form the load steps consume (F17b.v f17_rd). *)
Lemma f17F_rd : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H Hl. subst n.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as HH.
  rewrite Z.add_0_r, skipn_O, firstn_all in HH. exact HH.
Qed.

(* One instrumented 1-byte shadow read of an addressable byte X (F17b.v f17_shadow). *)
Lemma f17F_shadow : forall m X, addressable m X 1 ->
  exists b : byte, ov_read_bytes rsegs m (wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b]
    /\ (bv_signed b = 0 \/ X mod 8 < bv_signed b) /\ -128 <= bv_signed b < 128.
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & IS).
  exists b. split; [| split].
  - pose proof (cells_at_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes] in H. rewrite Z.add_0_r in H. exact H.
  - destruct OK as [H|H]; [left; exact H | right; lia].
  - pose proof (sbyte_range b); lia.
Qed.

(* One loaded record byte, as the model's `bat` (F17b.v f17_byte_word / f17_beq_val / f17_bne_val / f17_bltu22). *)
Lemma f17F_byte_word : forall (l : list byte) (k : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn (Z.to_nat k) l)))) = Z_to_bv 64 (RF.bat l k).
Proof.
  intros l k Hk Hl.
  rewrite (F17b.f17_fs1 l (Z.to_nat k) (Z_to_bv 8 0) Hl).
  rewrite le_word_1, b_extract8_id, zext_small. reflexivity.
Qed.

Lemma f17F_beq_val : forall (l : list byte) (k c : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  0 <= c < 2 ^ 64 ->
  bv_eqb (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn (Z.to_nat k) l)))))
         (Z_to_bv 64 c)
    = (RF.bat l k =? c).
Proof.
  intros l k c Hk Hl Hc. rewrite (f17F_byte_word l k Hk Hl). unfold RF.bat.
  exact (rf_beq (nth (Z.to_nat k) l (Z_to_bv 8 0)) c Hc).
Qed.

Lemma f17F_bne_val : forall (l : list byte) (k c : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  0 <= c < 2 ^ 64 ->
  negb (bv_eqb (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn (Z.to_nat k) l)))))
               (Z_to_bv 64 c))
    = negb (RF.bat l k =? c).
Proof. intros l k c Hk Hl Hc. f_equal. exact (f17F_beq_val l k c Hk Hl Hc). Qed.

Lemma f17F_bltu22 : forall (l : list byte) (k : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  bv_ltu (Z_to_bv 64 22)
         (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn (Z.to_nat k) l)))))
    = negb (RF.bat l k <=? 22).
Proof.
  intros l k Hk Hl. rewrite (f17F_byte_word l k Hk Hl).
  pose proof (F17b.f17_bat_range l k) as HR.
  unfold bv_ltu. rewrite !unsigned_lit by lia.
  destruct (Z.leb_spec (RF.bat l k) 22) as [H|H]; cbn [negb];
    [apply Z.ltb_ge | apply Z.ltb_lt]; lia.
Qed.

(* The length-and-sum guard 0x82468 `sltiu a0,s4,50` / 0x82470 `or a0,a0,a1` (F17b.v f17_guard, over lib.Lib's
   value function). *)
Lemma f17F_guard : forall len s, 0 <= len < 2 ^ 64 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (LPE.v_sltiu (Z_to_bv 64 len) 50))
                    (bv_unsigned (Z_to_bv 64 (1 - b2z s))))
  = Z_to_bv 64 (if (50 <=? len) && s then 0 else 1).
Proof.
  intros len s Hlen. unfold LPE.v_sltiu.
  rewrite (unsigned_lit len) by lia. change (bv_wrap 64 50) with 50.
  destruct (Z.ltb_spec len 50) as [H|H].
  - replace (50 <=? len) with false by (symmetry; apply Z.leb_gt; lia).
    destruct s; cbn [andb b2z]; vm_compute; reflexivity.
  - replace (50 <=? len) with true by (symmetry; apply Z.leb_le; lia).
    destruct s; cbn [andb b2z]; vm_compute; reflexivity.
Qed.

(* ---- The stepping tactics of F17b.v, over evtF. ---- *)

Ltac set_conclF g' := change_no_check g'.
Ltac cbv_concl_iotaF :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv iota in g in set_conclF g'.

(* Discharge a `getr R k = getr regs k` goal where R is a bvmap_set chain over mkR_of regs (F17b.v regeq). *)
Ltac regeqF :=
  simp_regs;
  first [ reflexivity
        | symmetry; eassumption
        | symmetry; apply Regs6ss.mkR_of_eqv; reflexivity
        | eassumption
        | apply Regs6ss.mkR_of_eqv; reflexivity ].

(* The instrumented shadow check's bnez convergence (F17b.v converge). *)
Ltac convergeF scratch Xe b OK BD :=
  match goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr, evtF segs RNG Q (MS (bvmap_set scratch rr R) F cont fc rv m ro)) by
        (let K0 := fresh "K0" in
         destruct (Z.eqb_spec (bv_signed b) 0) as [K0|K0];
         [ match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold sxb; rewrite K0; vm_compute; reflexivity) end;
           cbv_concl_iotaF;
           match goal with |- evtF _ _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end
         | let Hmb := fresh "Hmb" in let Hlt := fresh "Hlt" in
           pose proof (Z.mod_pos_bound Xe 8 ltac:(lia)) as Hmb;
           assert (Hlt : Xe mod 8 < bv_signed b) by (destruct OK as [HH|HH]; [exfalso; apply K0; exact HH | lia]);
           match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold sxb; rewrite bv_eqb_lit by lia;
               replace (bv_signed b =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           cbv_concl_iotaF; step; step;
           match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (rewrite (unsigned_lit Xe) by (unfold APPMEM_END in *; lia);
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           cbv_concl_iotaF; step;
           match goal with |- evtF _ _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro.

(* Shadow check of the byte phi+kk (srli; add s10; lb; bnez slow); RSH gives the one-byte footprint of its
   metadata byte (the brief's shadow range, instantiated at kk: lia cannot compare two `Z.shiftr` atoms). *)
Ltac shadowcheckF phi mem Haddr RSH kk scratch :=
  step; step;
  rewrite (unsigned_lit (phi + kk)) by (unfold APPMEM_END in *; lia);
  let Had := fresh "Had" in let b := fresh "b" in let HRsh := fresh "HRsh" in
  let OK := fresh "OK" in let BD := fresh "BD" in let Rk := fresh "Rk" in
  assert (Had : addressable mem (phi + kk) 1) by (apply (addressable_sub mem phi 50 kk 1 Haddr); lia);
  destruct (f17F_shadow mem (phi + kk) Had) as (b & HRsh & OK & BD);
  pose proof (RSH kk ltac:(lia)) as Rk;
  step; step; convergeF scratch (phi + kk) b OK BD.

(* f_opens = false from the one failed test in the context (F17b.v fop_false). *)
Ltac fop_falseF :=
  apply F17b.f17_fopens_false; repeat (first [ left; assumption | right ]); assumption.

(* Drop the 1-byte read facts of a finished check and its shadow disjunction (F17b.v clr1). *)
Ltac clr1F := repeat match goal with
  | H : ov_read_bytes _ _ _ 1 = _ |- _ => clear H
  | H : bv_signed _ = 0 \/ _ |- _ => clear H
  end.

(* A failed byte test: the branch to 0x82634 is taken with memory unchanged and f_opens false. The state
   equality comes first, so that the register goals see an instantiated R. *)
Ltac f17_exitF := apply evtF_done; hnf; do 2 eexists; split;
  [ left; split; [reflexivity|]; split; [reflexivity | fop_falseF]
  | do 12 (split; [regeqF|]); regeqF ].

(* ---- The run. ---- *)

Lemma seg_F17b_pre_F : forall (RNG : footprint) (regs F : bvmap 5 word) (fc : bv 32)
    (mem : word -> option byte) (A phi fr len : Z) (gg : list byte) (s : bool),
  (* the cut's register values: s1 = A, s2 = Phi, s4 = len_j, s6 = 1, s10 = ASAN_K, s11 = -8 *)
  getr regs 9 = Z_to_bv 64 A -> getr regs 18 = Z_to_bv 64 phi -> getr regs 20 = Z_to_bv 64 len ->
  getr regs 22 = Z_to_bv 64 1 -> getr regs 26 = Z_to_bv 64 ASAN_K -> getr regs 27 = Z_to_bv 64 (-8) ->
  (* the cut's bounds *)
  0 <= A < APPMEM_END -> 0 <= len <= APPMEM_END ->
  AC.GT <= fr -> fr + 2920 <= APPMEM_END -> fr + FRAME_BYTES <= A ->
  (* the cut's memory facts *)
  s = (RM.blocksum (skipn 18 gg) =? 0) ->
  q64 mem (A + 248) (1 - b2z s) -> length gg = 50%nat ->
  (* The record Phi and the block spill exist only on a LONG frame (50 <= len_j): a short frame also reaches
     0x82468 and takes the guard exit at 0x82474 at once, reading nothing but [A + 248] (a Theorem Labs lane's gap
     report). So these six facts are stated under `50 <= len ->`. *)
  (50 <= len -> 0 < phi /\ phi + 50 <= APPMEM_END /\ (phi + 50 <= fr + 2880 \/ fr + 2920 <= phi) /\
     bytes_at rsegs mem phi gg /\ addressable mem phi 50 /\ q64 mem (A + 312) (phi + 18)) ->
  q64 mem (A + 168) (fr + 2880) -> q64 mem (A + 88) (fr + 2885) ->
  wr_at rsegs mem (fr + 2880) 40 -> (forall a, fr + 2880 <= a < fr + 2920 -> app_mem a) ->
  (* the footprint *)
  rng RNG (A + 248) 8 -> rng RNG (A + 312) 8 -> rng RNG (A + 168) 8 -> rng RNG (A + 88) 8 ->
  (* The record window [Phi+16, Phi+27) and its shadow bytes are read only on a LONG frame (50 <= len_j):
     the short arm takes the guard exit at 0x82474 at once and reads [A + 248] alone. So these two
     footprint facts are stated under `50 <= len ->` as well. *)
  (50 <= len -> rng RNG (phi + 16) 11 /\
     rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) (Z.shiftr (phi + 26) 3 - Z.shiftr (phi + 16) 3 + 1)) ->
  rng RNG (fr + 2880) 5 ->
  evtF rsegs RNG
    (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
       ((ms' = MS R F (Z_to_bv 64 0x82634) fc None m' (seg_rom rsegs) /\ m' = mem /\
         f_opens len gg = false)
        \/ (ms' = MS R F (Z_to_bv 64 ACPY.ASAN_MEMCPY) fc None m' (seg_rom rsegs) /\
            f_opens len gg = true /\
            getr R 1 = Z_to_bv 64 0x82634 /\ getr R 10 = Z_to_bv 64 (fr + 2885) /\
            getr R 11 = Z_to_bv 64 (phi + 27) /\ getr R 12 = Z_to_bv 64 (RF.bat gg 26) /\
            F17b.f17_mid fr gg mem m')) /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 27 = getr regs 27)
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x82468) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs F fc mem A phi fr len gg s E9 E18 E20 E22 E26 E27
    HAr Hlen HGTfr HfrE HfrA Hsum Q248 Hrblen HLONG Q168 Q88 Hwrf Happfr
    R248 R312 R168 R88 HRNGL Rfr.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  pose proof FRAME_BYTES_val as HFBv.
  assert (Hfr0 : 0 <= fr) by lia.
  (* the phi bounds and the per-byte shadow footprint are long-frame facts: see the `50 <= len` branch *)
  assert (HfrN : fr + 2920 <= 2 ^ 64) by (unfold APPMEM_END in HfrE; lia).
  assert (HAN : A + 440 <= 2 ^ 64) by (unfold APPMEM_END in HAr; lia).

  assert (Hs9r : Sem.reg_get regs (9%bv) = Z_to_bv 64 A) by (rewrite <- E9; unfold getr; reflexivity).
  assert (Hs18r : Sem.reg_get regs (18%bv) = Z_to_bv 64 phi) by (rewrite <- E18; unfold getr; reflexivity).
  assert (Hs20r : Sem.reg_get regs (20%bv) = Z_to_bv 64 len) by (rewrite <- E20; unfold getr; reflexivity).
  assert (Hs22r : Sem.reg_get regs (22%bv) = Z_to_bv 64 1) by (rewrite <- E22; unfold getr; reflexivity).
  assert (Hs26r : Sem.reg_get regs (26%bv) = Z_to_bv 64 ASAN_K) by (rewrite <- E26; unfold getr; reflexivity).
  assert (Hs27r : Sem.reg_get regs (27%bv) = Z_to_bv 64 (-8)) by (rewrite <- E27; unfold getr; reflexivity).
  assert (IDW : bvmap_set (9%bv) (Z_to_bv 64 A)
                 (bvmap_set (18%bv) (Z_to_bv 64 phi)
                   (bvmap_set (20%bv) (Z_to_bv 64 len)
                     (bvmap_set (22%bv) (Z_to_bv 64 1)
                       (bvmap_set (26%bv) (Z_to_bv 64 ASAN_K)
                         (bvmap_set (27%bv) (Z_to_bv 64 (-8)) (Regs6ss.mkR_of regs))))))
                = Regs6ss.mkR_of regs)
    by (rewrite <- Hs9r, <- Hs18r, <- Hs20r, <- Hs22r, <- Hs26r, <- Hs27r; cbn; reflexivity).
  rewrite <- IDW.
  (* 0x82468 sltiu a0,s4,50 ; 0x8246c ld a1,248(s1) ; 0x82470 or a0,a0,a1 ; 0x82474 bnez a0,82634 *)
  pose proof (f17F_rd mem (A + 248) _ 8 Q248 (length_le8 _)) as HR248.
  step. step. step. step.
  subst s.
  rewrite (f17F_guard len (RM.blocksum (skipn 18 gg) =? 0) ltac:(unfold APPMEM_END in *; lia)).
  destruct (Z.leb_spec 50 len) as [Hl50|Hl50].
  - (* a long frame: the record Phi, its bytes and the block spill are there *)
    destruct (HLONG ltac:(lia)) as (Hphipos & HphiE & Hphiwin & Hrbb & Haddr & Q312).
    destruct (HRNGL ltac:(lia)) as (Rrec & Rsh).
    assert (Hphi64 : phi + 50 <= 2 ^ 64) by (unfold APPMEM_END in HphiE; lia).
    (* the one-byte footprint of each checked metadata byte *)
    assert (RSH : forall k, 16 <= k <= 26 -> rng RNG (Z.shiftr (phi + k) 3 + ASAN_K) 1).
    { intros k Hk.
      apply (rng_sub' RNG (Z.shiftr (phi + 16) 3 + ASAN_K)
               (Z.shiftr (phi + 26) 3 - Z.shiftr (phi + 16) 3 + 1) _ _ Rsh).
      rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      unfold APPMEM_END in *. Z.div_mod_to_equations. lia. }
    destruct (RM.blocksum (skipn 18 gg) =? 0) eqn:ESUM.
    + (* the record is long and the block sum is 0: the opens_record body runs *)
      assert (Hbs : (RM.blocksum (skipn 18 gg) =? 0) = true) by exact ESUM.
      assert (H50t : (50 <=? len) = true) by (apply Z.leb_le; lia).
      rewrite Bool.andb_true_l.
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false by (symmetry; vm_compute; reflexivity) end; cbv_concl_iotaF.
      assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply unsigned_lit; unfold APPMEM_END in *; lia).
      assert (Ephi18 : bv_unsigned (Z_to_bv 64 (phi + 18)) = phi + 18)
        by (apply unsigned_lit; unfold APPMEM_END in *; lia).
      (* 0x82478 beqz s2,82fa0 (T29): Phi <> 0 *)
      step. if_false.
      (* 0x8247c li a0,-19 ; 0x82480 bltu a0,s2 (T30): Phi + 18 does not wrap *)
      step. step. if_false.
      (* 0x82484 li a0,-16 ; 0x82488 bgeu s2,a0 (T31): Phi + 16 does not wrap *)
      step. step. if_false.
      (* check 1: Phi+16 = 0xcd *)
      step. (* addi a0,s2,16 *)
      shadowcheckF phi mem Haddr RSH 16 (Z_to_bv 5 12).
      assert (Hrr16 : ov_read_bytes rsegs mem (wa (phi + 16)) 1
                        = Some (firstn 1 (skipn (Z.to_nat 16) gg))).
      { pose proof (bytes_at_ov_read rsegs mem phi gg (Z.to_nat 16) 1 Hrbb ltac:(lia)) as H.
        replace (phi + Z.of_nat (Z.to_nat 16)) with (phi + 16) in H by lia. exact H. }
      step. step. step.
      rewrite (f17F_bne_val gg 16 205 ltac:(lia) ltac:(lia) ltac:(lia)).
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb16 end;
        cbv_concl_iotaF; [ f17_exitF | ]. clr1F.
      (* 0x824ac li a0,-18 ; 0x824b0 bltu a0,s2 (T32) *)
      step. step. if_false.
      (* check 2: Phi+17 = 0xea *)
      step. shadowcheckF phi mem Haddr RSH 17 (Z_to_bv 5 12).
      assert (Hrr17 : ov_read_bytes rsegs mem (wa (phi + 17)) 1
                        = Some (firstn 1 (skipn (Z.to_nat 17) gg))).
      { pose proof (bytes_at_ov_read rsegs mem phi gg (Z.to_nat 17) 1 Hrbb ltac:(lia)) as H.
        replace (phi + Z.of_nat (Z.to_nat 17)) with (phi + 17) in H by lia. exact H. }
      step. step. step.
      rewrite (f17F_bne_val gg 17 234 ltac:(lia) ltac:(lia) ltac:(lia)).
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb17 end;
        cbv_concl_iotaF; [ f17_exitF | ]. clr1F.
      (* check 3: b = Phi+18, b[0] = 4 *)
      step. shadowcheckF phi mem Haddr RSH 18 (Z_to_bv 5 12).
      assert (Hrr18 : ov_read_bytes rsegs mem (wa (phi + 18)) 1
                        = Some (firstn 1 (skipn (Z.to_nat 18) gg))).
      { pose proof (bytes_at_ov_read rsegs mem phi gg (Z.to_nat 18) 1 Hrbb ltac:(lia)) as H.
        replace (phi + Z.of_nat (Z.to_nat 18)) with (phi + 18) in H by lia. exact H. }
      step. step. step.
      rewrite (f17F_bne_val gg 18 4 ltac:(lia) ltac:(lia) ltac:(lia)).
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb18 end;
        cbv_concl_iotaF; [ f17_exitF | ]. clr1F.
      (* 0x824f4 li a1,-1 ; 0x824f8 beq a0,a1 (T33) *)
      step. step. if_false.
      (* check 4: b[1] = Phi[19] = s6 = 1 *)
      step. shadowcheckF phi mem Haddr RSH 19 (Z_to_bv 5 13).
      assert (Hrr19 : ov_read_bytes rsegs mem (wa (phi + 19)) 1
                        = Some (firstn 1 (skipn (Z.to_nat 19) gg))).
      { pose proof (bytes_at_ov_read rsegs mem phi gg (Z.to_nat 19) 1 Hrbb ltac:(lia)) as H.
        replace (phi + Z.of_nat (Z.to_nat 19)) with (phi + 19) in H by lia. exact H. }
      step. step.
      rewrite (f17F_bne_val gg 19 1 ltac:(lia) ltac:(lia) ltac:(lia)).
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb19 end;
        cbv_concl_iotaF; [ f17_exitF | ]. clr1F.
      (* 0x82518 li a1,-5 ; 0x8251c bltu a1,a0 (T34) *)
      step. step. if_false.
      (* check 5: b[4] = Phi[22] = 0 *)
      step. shadowcheckF phi mem Haddr RSH 22 (Z_to_bv 5 13).
      assert (Hrr22 : ov_read_bytes rsegs mem (wa (phi + 22)) 1
                        = Some (firstn 1 (skipn (Z.to_nat 22) gg))).
      { pose proof (bytes_at_ov_read rsegs mem phi gg (Z.to_nat 22) 1 Hrbb ltac:(lia)) as H.
        replace (phi + Z.of_nat (Z.to_nat 22)) with (phi + 22) in H by lia. exact H. }
      step. step.
      rewrite (f17F_bne_val gg 22 0 ltac:(lia) ltac:(lia) ltac:(lia)).
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb22 end;
        cbv_concl_iotaF; [ f17_exitF | ]. clr1F.
      (* 0x8253c li a1,-6 ; 0x82540 bltu a1,a0 (T35) *)
      step. step. if_false.
      (* check 6: b[5] = Phi[23] = 2 *)
      step. shadowcheckF phi mem Haddr RSH 23 (Z_to_bv 5 13).
      assert (Hrr23 : ov_read_bytes rsegs mem (wa (phi + 23)) 1
                        = Some (firstn 1 (skipn (Z.to_nat 23) gg))).
      { pose proof (bytes_at_ov_read rsegs mem phi gg (Z.to_nat 23) 1 Hrbb ltac:(lia)) as H.
        replace (phi + Z.of_nat (Z.to_nat 23)) with (phi + 23) in H by lia. exact H. }
      step. step. step.
      rewrite (f17F_bne_val gg 23 2 ltac:(lia) ltac:(lia) ltac:(lia)).
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb23 end;
        cbv_concl_iotaF; [ f17_exitF | ]. clr1F.
      (* 0x82564 li a1,-7 ; 0x82568 bltu a1,a0 (T36) *)
      step. step. if_false.
      (* check 7: b[6] = Phi[24] = 0 *)
      step. shadowcheckF phi mem Haddr RSH 24 (Z_to_bv 5 13).
      assert (Hrr24 : ov_read_bytes rsegs mem (wa (phi + 24)) 1
                        = Some (firstn 1 (skipn (Z.to_nat 24) gg))).
      { pose proof (bytes_at_ov_read rsegs mem phi gg (Z.to_nat 24) 1 Hrbb ltac:(lia)) as H.
        replace (phi + Z.of_nat (Z.to_nat 24)) with (phi + 24) in H by lia. exact H. }
      step. step.
      rewrite (f17F_bne_val gg 24 0 ltac:(lia) ltac:(lia) ltac:(lia)).
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb24 end;
        cbv_concl_iotaF; [ f17_exitF | ]. clr1F.
      (* 0x82588 bltu s11,a0 (T37, s11 = -8) *)
      step. if_false.
      (* check 8: b[7] = Phi[25] = 0xfe *)
      step. shadowcheckF phi mem Haddr RSH 25 (Z_to_bv 5 13).
      assert (Hrr25 : ov_read_bytes rsegs mem (wa (phi + 25)) 1
                        = Some (firstn 1 (skipn (Z.to_nat 25) gg))).
      { pose proof (bytes_at_ov_read rsegs mem phi gg (Z.to_nat 25) 1 Hrbb ltac:(lia)) as H.
        replace (phi + Z.of_nat (Z.to_nat 25)) with (phi + 25) in H by lia. exact H. }
      step. step. step.
      rewrite (f17F_bne_val gg 25 254 ltac:(lia) ltac:(lia) ltac:(lia)).
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb25 end;
        cbv_concl_iotaF; [ f17_exitF | ]. clr1F.
      (* 0x825ac li a1,-9 ; 0x825b0 bltu a1,a0 (T38) *)
      step. step. if_false.
      (* check 9a: b[8] = Phi[26] into a1, beqz a1 -> 0x82634 *)
      step. shadowcheckF phi mem Haddr RSH 26 (Z_to_bv 5 13).
      assert (Hrr26 : ov_read_bytes rsegs mem (wa (phi + 26)) 1
                        = Some (firstn 1 (skipn (Z.to_nat 26) gg))).
      { pose proof (bytes_at_ov_read rsegs mem phi gg (Z.to_nat 26) 1 Hrbb ltac:(lia)) as H.
        replace (phi + Z.of_nat (Z.to_nat 26)) with (phi + 26) in H by lia. exact H. }
      step. step.
      rewrite (f17F_beq_val gg 26 0 ltac:(lia) ltac:(lia) ltac:(lia)).
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb26a end;
        cbv_concl_iotaF; [ f17_exitF | ]. clr1F.
      (* 0x825d0 beq a0,s11 (T39) *)
      step. if_false.
      (* check 9b: 0x825d4 li a0,22 ; 0x825d8 bltu a0,a1,82634 *)
      step. step.
      rewrite (f17F_bltu22 gg 26 ltac:(lia) ltac:(lia)).
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb26b end;
        cbv_concl_iotaF; [ f17_exitF | ]. clr1F.
      (* every test passed: the record opens *)
      assert (Hop : f_opens len gg = true)
        by exact (F17b.f17_fopens_true _ _ H50t Hb16 Hb17 Hb18 Hb19 Hb22 Hb23 Hb24 Hb25 Hb26a Hb26b Hbs).
      assert (Hn26 : 1 <= RF.bat gg 26 <= 22).
      { pose proof (F17b.f17_bat_range gg 26) as Hr.
        apply Z.eqb_neq in Hb26a. apply Bool.negb_false_iff, Z.leb_le in Hb26b. lia. }
      clear HR248.
      destruct (Tac_f17b.f17m_meta_bytes mem (phi + 26)
                  (addressable_sub mem phi 50 26 1 Haddr ltac:(lia) ltac:(lia) ltac:(lia)))
        as (b26 & Hsb26 & OK26 & BD26).
      (* 0x825dc ld a0,312(s1) ; 0x825e0 addi a0,a0,8 ; 0x825e4 ld a1,168(s1) *)
      pose proof (f17F_rd mem (A + 312) _ 8 Q312 (length_le8 _)) as HR312.
      step. clear HR312.
      step.
      pose proof (f17F_rd mem (A + 168) _ 8 Q168 (length_le8 _)) as HR168.
      step. clear HR168.
      (* 0x825e8 sw s6,0(a1): have = 1 at fr + 2880 *)
      assert (HS0 : store_ok rsegs mem (wa (fr + 2880)) 4 = true).
      { replace (fr + 2880) with (fr + 2880 + 0) by lia.
        apply (wr_at_store_ok rsegs mem (fr + 2880) 40 0 4 Hwrf); lia. }
      assert (HS0' : store_ok rsegs mem (wa (fr + 2880 + 0)) 4 = true)
        by (apply (wr_at_store_ok rsegs mem (fr + 2880) 40 0 4 Hwrf); lia).
      step.
      remember (write_to_mem mem (wa (fr + 2880)) (le4 (Z_to_bv 64 1))) as M1 eqn:EM1.
      assert (MU1 : munch [(fr + 2880, fr + 2885)] mem M1).
      { rewrite EM1. apply munch_write; [apply munch_refl | lia | rewrite length_le4; lia
        | cbn [inside]; left; rewrite length_le4; lia]. }
      assert (HfrO : forall x, x < fr + 2880 \/ fr + 2885 <= x -> outside [(fr + 2880, fr + 2885)] x)
        by (intros x Hx; apply F17b.f17_out1; exact Hx).
      assert (HshO : forall x, in_shadow x -> outside [(fr + 2880, fr + 2885)] x).
      { intros x Hx. apply HfrO.
        destruct (Z_lt_le_dec x (fr + 2880)) as [L|L]; [left; exact L|].
        destruct (Z_lt_le_dec x (fr + 2885)) as [L2|L2]; [|right; exact L2].
        exfalso. exact (app_not_shadow x (Happfr x ltac:(lia)) Hx). }
      assert (Hap26 : app_mem (phi + 26)).
      { pose proof Haddr as (_ & _ & _ & Hab). destruct (Hab 26 ltac:(lia)) as (Hap & _). exact Hap. }
      assert (HshE : Z.shiftr (phi + 26) 3 + ASAN_K = shadow_addr (phi + 26))
        by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      assert (HRs26 : ov_read_bytes rsegs M1 (wa (Z.shiftr (phi + 26) 3 + ASAN_K)) 1 = Some [b26]).
      { apply (f17F_rd M1 _ [b26] 1); [|reflexivity].
        eapply fl_bytes; [exact Hsb26 | exact MU1 |]. cbn [length]. intros x Hx.
        apply HshO. replace x with (shadow_addr (phi + 26)) by (rewrite <- HshE; lia).
        apply shadow_of_app. exact Hap26. }
      assert (Q312a : q64 M1 (A + 312) (phi + 18)).
      { unfold q64 in *. eapply fl_bytes; [exact Q312 | exact MU1 |].
        rewrite length_le8. intros x Hx. apply HfrO. right. lia. }
      assert (Q168a : q64 M1 (A + 168) (fr + 2880)).
      { unfold q64 in *. eapply fl_bytes; [exact Q168 | exact MU1 |].
        rewrite length_le8. intros x Hx. apply HfrO. right. lia. }
      assert (Q88a : q64 M1 (A + 88) (fr + 2885)).
      { unfold q64 in *. eapply fl_bytes; [exact Q88 | exact MU1 |].
        rewrite length_le8. intros x Hx. apply HfrO. right. lia. }
      assert (Hrbb1 : bytes_at rsegs M1 phi gg).
      { eapply fl_bytes; [exact Hrbb | exact MU1 |]. rewrite Hrblen. intros x Hx. apply HfrO.
        destruct Hphiwin as [Hd|Hd]; [left|right]; lia. }
      (* 0x825ec li a1,9 ; 0x825f0 bltu a0,a1 (T40) *)
      assert (Ephi26 : bv_unsigned (Z_to_bv 64 (phi + 26)) = phi + 26)
        by (apply unsigned_lit; unfold APPMEM_END in *; lia).
      step. step. if_false.
      (* the shadow check of Phi + 26: srli a1,a0,3 ; add a1,a1,s10 ; lb a1,0(a1) ; bnez a1,82ea0 *)
      step. step.
      rewrite Ephi26.
      pose proof (RSH 26 ltac:(lia)) as R26.
      step. step.
      match goal with
      | |- evtF ?segs ?RNG0 ?Q (MS ?R ?F0 (if _ then _ else ?cont) ?fc0 ?rv ?m ?ro) =>
          enough (Gc : forall rr, evtF segs RNG0 Q (MS (bvmap_set (Z_to_bv 5 12) rr R) F0 cont fc0 rv m ro))
      end.
      2:{ intro rr26. clear OK26.
          assert (HRb26 : ov_read_bytes rsegs M1 (wa (phi + 26)) 1
                            = Some (firstn 1 (skipn (Z.to_nat 26) gg))).
          { pose proof (bytes_at_ov_read rsegs M1 phi gg (Z.to_nat 26) 1 Hrbb1 ltac:(lia)) as H.
            replace (phi + Z.of_nat (Z.to_nat 26)) with (phi + 26) in H by lia. exact H. }
          (* 0x82604 ld a1,312(s1) ; 0x82608 lbu a2,8(a1) ; 0x8260c ld a0,168(s1) *)
          pose proof (f17F_rd M1 (A + 312) _ 8 Q312a (length_le8 _)) as HR312a.
          step. clear HR312a.
          step. clear HRb26.
          pose proof (f17F_rd M1 (A + 168) _ 8 Q168a (length_le8 _)) as HR168a.
          step. clear HR168a.
          rewrite (f17F_byte_word gg 26 ltac:(lia) ltac:(lia)).
          (* 0x82610 sb a2,4(a0): n at fr + 2884 *)
          assert (HSt4 : store_ok rsegs M1 (wa (fr + 2880 + 4)) 1 = true).
          { rewrite EM1. apply (wr_at_store_ok rsegs _ (fr + 2880) 40 4 1);
              [apply wr_at_write; exact Hwrf | lia | lia]. }
          assert (HSt4' : store_ok rsegs M1 (wa (fr + 2884)) 1 = true)
            by (replace (fr + 2884) with (fr + 2880 + 4) by lia; exact HSt4).
          step.
          match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => remember m2 as M2 eqn:EM2 end.
          assert (MU2 : munch [(fr + 2880, fr + 2885)] M1 M2).
          { rewrite EM2. apply munch_write; [apply munch_refl | lia
            | rewrite ?length_le1; cbn [length]; lia
            | cbn [inside]; left; rewrite ?length_le1; cbn [length]; lia]. }
          assert (MU12 : munch [(fr + 2880, fr + 2885)] mem M2) by exact (munch_trans _ _ _ _ MU1 MU2).
          assert (Q312b : q64 M2 (A + 312) (phi + 18)).
          { unfold q64 in *. eapply fl_bytes; [exact Q312 | exact MU12 |].
            rewrite length_le8. intros x Hx. apply HfrO. right. lia. }
          assert (Q88b : q64 M2 (A + 88) (fr + 2885)).
          { unfold q64 in *. eapply fl_bytes; [exact Q88 | exact MU12 |].
            rewrite length_le8. intros x Hx. apply HfrO. right. lia. }
          (* 0x82614 beqz a1 (T41) *)
          step. if_false.
          (* 0x82618 li a0,-10 ; 0x8261c ld a1,312(s1) ; 0x82620 bltu a0,a1 (T42) *)
          step.
          pose proof (f17F_rd M2 (A + 312) _ 8 Q312b (length_le8 _)) as HR312b.
          step. step. if_false.
          (* 0x82624 ld a1,312(s1) ; 0x82628 addi a1,a1,9 ; 0x8262c ld a0,88(s1) ; 0x82630 jal __asan_memcpy *)
          step. clear HR312b. step.
          pose proof (f17F_rd M2 (A + 88) _ 8 Q88b (length_le8 _)) as HR88b.
          step. clear HR88b. step.
          (* at the callee entry: the pre-call stretch is done *)
          assert (WM1 : wmono rsegs mem M1) by (rewrite EM1; apply wmono_write; apply wmono_refl).
          assert (WM2 : wmono rsegs M1 M2) by (rewrite EM2; apply wmono_write; apply wmono_refl).
          assert (WM12 : wmono rsegs mem M2) by exact (wmono_trans rsegs _ _ _ WM1 WM2).
          apply evtF_done. hnf. do 2 eexists. split.
          { right. split; [reflexivity|]. split; [exact Hop|].
            split; [regeqF|]. split; [regeqF|]. split; [regeqF|]. split; [regeqF|].
            unfold F17b.f17_mid. split; [exact MU12|]. split; [exact WM12|].
            split.
            { unfold u32. rewrite EM2.
              apply (bytes_at_write_other rsegs M1 (fr + 2884) _ (fr + 2880) _);
                [rewrite EM1; apply bytes_at_write_same; [lia | rewrite length_le4; lia]
                | lia | rewrite length_le1; lia | rewrite length_le4, length_le1; lia]. }
            { unfold b8. rewrite EM2.
              replace (le1 (Z_to_bv 64 (RF.bat gg 26))) with [Z_to_bv 8 (RF.bat gg 26)]
                by (unfold le1; cbn [Z_to_le_bytes];
                    rewrite unsigned_lit by (pose proof (F17b.f17_bat_range gg 26); lia); reflexivity).
              apply (bytes_at_write_same rsegs M1 (fr + 2884)); [lia | cbn [length]; lia]. } }
          do 12 (split; [regeqF|]); regeqF. }
      destruct (Z.eqb_spec (bv_signed b26) 0) as [K0|K0].
      -- match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
           replace c with false by (unfold sxb; rewrite K0; vm_compute; reflexivity) end;
         cbv_concl_iotaF;
         match goal with |- evtF _ _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 (Z_to_bv 5 12))) end.
      -- assert (Hlt26 : (phi + 26) mod 8 < bv_signed b26) by
           (pose proof (Z.mod_pos_bound (phi + 26) 8 ltac:(lia)); destruct OK26 as [HH|HH];
            [exfalso; apply K0; exact HH | lia]).
         match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
           replace c with true by (unfold sxb; rewrite bv_eqb_lit by (pose proof BD26; lia);
             replace (bv_signed b26 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
         cbv_concl_iotaF.
         step. (* andi a2,a0,7 *)
         step. (* blt a2,a1,82604 *)
         match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
           replace c with true by (unfold APPMEM_END in HphiE;
             rewrite (unsigned_lit (phi + 26)) by lia; rewrite land7 by lia; rewrite lts_sxb by lia;
             symmetry; apply Z.ltb_lt; lia) end;
         cbv_concl_iotaF;
         match goal with |- evtF _ _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 (Z_to_bv 5 12))) end.
    + (* the block sum is nonzero: [A+248] = 1, the guard exits at 0x82634 with memory unchanged *)
      assert (Hbs : (RM.blocksum (skipn 18 gg) =? 0) = false) by exact ESUM.
      rewrite Bool.andb_true_l.
      match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with true by (symmetry; vm_compute; reflexivity) end; cbv_concl_iotaF.
      f17_exitF.
  - (* the record is short (len < 50): the guard exits at 0x82634 with memory unchanged *)
    assert (H50f : (50 <=? len) = false) by (apply Z.leb_gt; lia).
    rewrite Bool.andb_false_l.
    match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by (symmetry; vm_compute; reflexivity) end; cbv_concl_iotaF.
    f17_exitF.
Qed.

(* The footprint twin of F17b.v:76 (f17_lu_evt): the bridge takes a footprint run of the lib.Lib engine, through
   lib.Lib's Exec.evt. No _F ever steps through a callee, and this one steps nothing at all. *)
Lemma f17_lu_evt_F : forall RNG Q ms, evtF rsegs RNG Q ms -> UEx.evt rsegs Q ms.
Proof. intros RNG Q ms H. exact (F17b.f17_lu_evt Q ms (evtF_evt rsegs RNG Q ms H)). Qed.
