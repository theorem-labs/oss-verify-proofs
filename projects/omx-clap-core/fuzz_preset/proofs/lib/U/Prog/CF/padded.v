From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memcpy_c memset_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import padded_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* The walk of padded (ubsan #102, entry 0x1448c, 37 instructions, frame 0x30 = 48; padded_c.v has the measurement):
     0x1448c .. 0x144b4  addi sp, sp, -0x30; sd ra, s0, s1, s2, s3 at sp + 0x28 .. sp + 8; s1 = fill, s2 = size,
                         s3 = data; a0 = size + 16; jal malloc (0x18390), ra = 0x144b8.
     0x144b8 .. 0x14518  s0 = a0; beqz a0 (the NULL arm 0x144f0, which stores 1 into g_own_ran_out, is not taken:
                         malloc_contract_r returns a non-NULL block under rf_room); beqz s2 skips memcpy (0x22520) of
                         size bytes from data when size = 0; UBSan's pointer-overflow test `not a0, s0; bltu a0, s2`
                         (trap 0x1451c) is not taken because q + size + 16 <= alloc_ceiling < 2 ^ 63; memset (0x22924)
                         of 16 bytes of fill at s0 + size; j 0x144fc; a0 = s0; restore ra, s0 .. s3; return.
   The part from 0x144b8 writes only the new block; the prologue writes only the 40 bytes of saved registers.
   The CF form: lib/U/Prog/padded.v's walk with SRCF's SR (imported last), for lib/U/Prog/CF/padded_c.v. *)

Ltac pd_br := unfold_cond; rewrite ?unsigned_lit by lia.

Ltac pd_fixS :=
  repeat match goal with |- context [Z_to_bv 64 (?x + -48 + 48)] => replace (x + -48 + 48) with x by lia end.

Lemma pd_rw_cut : forall m A (n k : Z) junk, 0 <= n -> 0 <= k ->
  rw_cells rsegs m A [CB (Z.to_nat (n + k)) junk] ->
  rw_cells rsegs m A [CB (Z.to_nat n) (firstn (Z.to_nat n) junk)] /\
  rw_cells rsegs m (A + n) [CB (Z.to_nat k) (skipn (Z.to_nat n) junk)].
Proof.
  intros m A n k junk Hn Hk [[Hwf Hb] Hw].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct Hw as (W1 & W2 & W). cbn [cells_size csize] in W1, W2, W.
  rewrite <- (firstn_skipn (Z.to_nat n) junk) in Hb.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [B1 B2].
  rewrite length_firstn in B2. replace (Nat.min (Z.to_nat n) (length junk)) with (Z.to_nat n) in B2 by lia.
  rewrite Z2Nat.id in B2 by lia.
  split; split; [split| |split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
  - cbn [cells_wf cell_wf]. split; [rewrite length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + n + i) with (A + (n + i)) by lia. apply W. lia.
Qed.

Lemma pd_rw_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma pd_join : forall m q n x fill, length x = Z.to_nat n -> 0 <= n -> 0 <= fill < 256 ->
  bytes_at rsegs m q x ->
  rw_cells rsegs m (q + n) [CB (Z.to_nat 16) (repeat (Z_to_bv 8 (fill mod 256)) (Z.to_nat 16))] ->
  bytes_at rsegs m q (x ++ repeat (Z_to_bv 8 fill) 16).
Proof.
  intros m q n x fill SL Hn Hf B R. apply (proj2 (bytes_at_app rsegs _ _ _ _)). split; [exact B|].
  rewrite SL, Z2Nat.id by lia. rewrite Z.mod_small in R by lia. exact (pd_rw_bytes _ _ _ _ R).
Qed.

Lemma pd_not_ltu : forall q n, 0 <= q -> 0 <= n -> q + n < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 q)) 18446744073709551615)) (Z_to_bv 64 n) = false.
Proof.
  intros q n Hq Hn Hqn. unfold bv_ltu.
  rewrite (unsigned_lit q) by lia. rewrite lnot_mod64 by lia.
  rewrite (unsigned_lit n) by lia.
  rewrite unsigned_lit by (apply Z.mod_pos_bound; lia).
  apply Z.ltb_ge. pose proof (Z.add_lnot_diag q) as E.
  rewrite <- (Z.mod_add (Z.lnot q) 1 (2 ^ 64)) by lia.
  rewrite Z.mod_small by (clear - E Hq Hn Hqn; lia).
  clear - E Hq Hn Hqn. lia.
Qed.

(* [not a0, s0; bltu a0, s2, unimp]: UBSan's pointer-overflow test, not taken when q + n < 2 ^ 64. *)
Ltac pd_ovf :=
  step; step;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "OV" in
      assert (H : c = false) by (apply pd_not_ltu; lia);
      rewrite H; cbv iota; clear H
  end.

Ltac pd_call_memcpy MC x j :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MC with (src := x) (junk := j); rewrite ?unsigned_lit by lia; first [eassumption | lia]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memcpy_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.

Ltac pd_call_memset MS0 j :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MS0 with (junk := j); rewrite ?unsigned_lit by lia; eassumption
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memset_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.

(* 0x1448c .. 0x144b4: the prologue (sp -= 0x30; ra, s0, s1, s2, s3 saved at sp + 0x28 .. sp + 8), s1 = fill,
   s2 = n, s3 = d, a0 = n + 16, and malloc (0x18390) with ra = 0x144b8. *)
Definition pd0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (d n fill : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x144b8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 (Z_to_bv 64 fill)
                  (Z_to_bv 64 (n + 16)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 n) (Z_to_bv 64 d)
                  s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x18390) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -40, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma pd_seg0 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d n fill : Z) (j : list byte),
  0 <= n <= 2 ^ 28 -> 48 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned sp + -40) [CB 40 j] ->
  evt rsegs (pd0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d n fill)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) (Z_to_bv 64 fill) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1448c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n fill j
    Hn Hsp FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -40, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply (rw_cells_split_CB rsegs _ _ [] 40%nat j [] [8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 11 step.
  finish.
Qed.

(* 0x144b8 .. 0x14518 with a0 = q <> 0: the copy into the block q, the fill, and the return. *)
Definition pd1_post (rav gp tp s0v s1v s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (S q n : Z) (x : list byte) (fill : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav (Z_to_bv 64 S) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
                  s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom rsegs) /\
    munch [(q, q + n + 16)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    bytes_at rsegs m' q (x ++ repeat (Z_to_bv 8 fill) 16).

Section Copy.
Hypothesis MC : memcpy_contract.
Hypothesis MS0 : memset_contract.

Lemma pd_seg1 : forall ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S q d n fill : Z)
    (x junk : list byte),
  48 <= S -> S < 2 ^ 64 ->
  0 < q -> q + n + 16 <= S + -48 -> 0 <= n -> 0 <= d -> d + n <= 2 ^ 64 -> 0 <= fill < 256 ->
  length x = Z.to_nat n -> bytes_at rsegs m d x ->
  rw_cells rsegs m q [CB (Z.to_nat (n + 16)) junk] ->
  (n = 0 \/ d + n <= q \/ q + n + 16 <= d) -> mem_inv rsegs m ->
  bytes_at rsegs m (S + -40) (le8 s3v ++ le8 s2v ++ le8 s1v ++ le8 s0v ++ le8 rav) ->
  evt rsegs (pd1_post rav gp tp s0v s1v s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 F fc m S q n x fill)
    (MS (mkR ra (Z_to_bv 64 (S + -48)) gp tp t0 t1 t2 s0 (Z_to_bv 64 fill) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 n) (Z_to_bv 64 d) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x144b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v s2v s3v F fc m
    S q d n fill x junk HS1 HS2 Hq Hqn Hn Hd Hdn Hf SL SRC DST DS MI BY.
  assert (RO : ro_cells rsegs m (S + -40) [C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]).
  { split; [cbn [cells_wf cell_wf]; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BY. }
  clear BY.
  pose proof (munch_refl [(q, q + n + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (pd_rw_cut m q n 16 junk Hn ltac:(lia) DST) as [D1 D2]. clear DST.
  step.
  step. pd_br. if_false.
  step.
  destruct (Z.eq_dec n 0) as [N0|N0].
  - destruct x as [|b x]; [|cbn [length] in SL; lia].
    pd_br. if_true.
    pd_ovf.
    do 4 step.
    pd_call_memset MS0 (skipn (Z.to_nat n) junk).
    do 9 step.
    pd_fixS.
    finish.
    all: apply (pd_join _ q n); [cbn [length]; lia | lia | lia | apply bytes_at_nil; lia | eassumption].
  - pd_br. if_false.
    do 4 step.
    pd_call_memcpy MC x (firstn (Z.to_nat n) junk).
    pd_ovf.
    do 4 step.
    pd_call_memset MS0 (skipn (Z.to_nat n) junk).
    do 9 step.
    pd_fixS.
    finish.
    all: apply (pd_join _ q n); [exact SL | lia | lia | eapply pd_rw_bytes; eassumption | eassumption].
Qed.

End Copy.

Ltac pd_cs tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [tac .. |];
  let Hr' := fresh "Hr" in
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; tac.

Section PD.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis HERR : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis HMAL : ms_malloc B = 0x18390.
Hypothesis MALLOC : forall fx : YK11.FPState, @malloc_contract_r fx rc B API F.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis MEMSET : memset_contract.

Lemma pd_img : img_low B.
Proof.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite HS. vm_compute. reflexivity.
  - pose proof YM05.alloc_ceiling_value. lia.
Qed.

Lemma pd_seg_in_img : forall a seg, find_segment (ms_segs B) a 1 = Some seg -> in_img B a.
Proof.
  intros a seg E. destruct (kb_find_segment _ a 1 seg E) as (Hin & H1 & H2).
  assert (C : forallb (fun s => existsb (fun rr => (bv_unsigned (fst rr) <=? Z.of_N (seg_base s)) &&
      (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst rr) + bv_unsigned (snd rr)))
      (segments_reserved (ms_segs B))) (ms_segs B) = true) by (rewrite HS; vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply existsb_exists in C. destruct C as (rr & Hr & Hc).
  apply andb_prop in Hc as (Hc1 & Hc2). apply Z.leb_le in Hc1, Hc2.
  split; [intros E'; rewrite E' in Hin; destruct Hin | exists rr; split; [exact Hr | lia]].
Qed.

Lemma pd_ro_false : forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hn. unfold ro_addr. rewrite unsigned_lit by lia. rewrite <- HS.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; exact (Hn (pd_seg_in_img a seg E)) | reflexivity].
Qed.

Lemma pd_present_of_writable : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a ->
  writable_at (ms_segs B) m a -> present m a.
Proof.
  intros m a Ha Hn W. unfold writable_at, wview in W. unfold present.
  destruct (m (Z_to_bv 64 a)) as [v|] eqn:E; [exists v; reflexivity|]. exfalso.
  rewrite unsigned_lit in W by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:Fs; [|apply W; reflexivity].
  exact (Hn (pd_seg_in_img a seg Fs)).
Qed.

Lemma pd_present_norm : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> present m a -> present (normalize rsegs m) a.
Proof. intros m a Ha Hn [v Hv]. exists v. unfold normalize. rewrite (pd_ro_false a Ha Hn). exact Hv. Qed.

Lemma pd_rw_of_present : forall m lo k, 0 <= lo -> lo + k <= 2 ^ 64 -> 0 <= k ->
  (forall i, 0 <= i < k -> present m (lo + i)) -> exists junk, rw_cells rsegs m lo [CB (Z.to_nat k) junk].
Proof.
  intros m lo k Hlo Hhi Hk HP.
  assert (ST : stk rsegs m lo (lo + k)).
  { split; [lia|]. split; [lia|]. intros a Ha. destruct (HP (a - lo)) as [v Hv]; [lia|].
    replace (lo + (a - lo)) with a in Hv by lia. unfold wa. split.
    - unfold wview. rewrite Hv. discriminate.
    - exists v. unfold mrd. rewrite Hv. reflexivity. }
  destruct (stk_carve rsegs m lo (lo + k) (Z.to_nat k) ST ltac:(lia)) as [_ [junk H]].
  exists junk. replace (lo + k - Z.of_nat (Z.to_nat k)) with lo in H by lia. exact H.
Qed.

Lemma pd_ro_agree_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> ~ in_img B a) -> ro_agree rsegs m'.
Proof.
  intros W m m' H HM HW a Ha. destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - pose proof (H a Ha) as E. unfold mrd in *. rewrite (HM a Ho). exact E.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (pd_ro_false (bv_unsigned a) Hr (HW _ Hr Ho)) as E. rewrite Z_to_bv_bv_unsigned in E. congruence.
Qed.

Lemma pd_bytes_frame : forall m m' a bs, bytes_at (ms_segs B) m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  bytes_at (ms_segs B) m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) Hm. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). exact (Hm (Z.of_nat i) ltac:(lia)).
Qed.

Lemma pd_run_n : forall (fx : YK11.FPState) regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop)
    (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) mem ->
  evt (ms_segs B) (fun ms => exists R pc' mem', ms = MS R (@fp_regs fx) pc' (@fp_csr fx) None mem'
                                                 (YK11.seg_rom (ms_segs B)) /\ K R pc' mem')
    (MS (rmk regs) (@fp_regs fx) pc (@fp_csr fx) None (normalize (ms_segs B) mem) (YK11.seg_rom (ms_segs B))) ->
  (forall R pc' m0 mem' regs', K R pc' m0 -> mem_rel (ms_segs B) mem' m0 -> ro_same (ms_segs B) mem mem' ->
     (forall r, YK11.getr regs' r = YK11.getr R r) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx regs' pc' mem' (YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs pc mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx regs pc mem md K P Hh Hl RA HE HK.
  apply (kb_run B regs pc mem md
    (fun R pc' mem' => exists m0, K R pc' m0 /\ mem_rel (ms_segs B) mem' m0 /\ ro_same (ms_segs B) mem mem') P Hh Hl).
  - eapply evt_mono; [apply (evt_normalize (ms_segs B)); [rewrite HS; vm_compute; reflexivity | exact RA | exact HE] |].
    intros s (s0 & (R & pc' & m0 & -> & HKR) & HREL & HRS).
    destruct s as [R1 F1 pc1 sv1 rv1 fc1 m1 ro1]. destruct HREL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in *. subst.
    exists R, pc', m1. split; [reflexivity|]. exists m0. split; [exact HKR|]. split; [exact E8 | exact HRS].
  - intros R pc' mem' regs' (m0 & HKR & HREL & HRS) HG. exact (HK R pc' m0 mem' regs' HKR HREL HRS HG).
Qed.

Lemma pd_back : forall m mr m0 W, ro_agree (ms_segs B) m -> mem_rel (ms_segs B) mr m0 -> ro_same (ms_segs B) m mr ->
  munch W (normalize (ms_segs B) m) m0 -> wmono (ms_segs B) (normalize (ms_segs B) m) m0 ->
  munch W m mr /\ wmono (ms_segs B) m mr /\ ro_agree (ms_segs B) mr.
Proof.
  intros m mr m0 W HA HR HS0 MU WM. pose proof (mem_rel_normalize (ms_segs B) m HA) as HN.
  split; [exact (munch_rel (ms_segs B) W m (normalize (ms_segs B) m) mr m0 HN HR HS0 MU)|].
  split; [exact (wmono_rel (ms_segs B) m (normalize (ms_segs B) m) mr m0 HN HR HS0 WM)|].
  exact (ro_agree_same (ms_segs B) m mr HA HS0).
Qed.

Lemma pd_blocks_user : forall L A p k, In (p, k) (blocks L A) -> exists q, In (q, k) (user_blocks A) /\ ptr_addr L q = p.
Proof.
  intros L A p k Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q k'] & E & Hq). cbn [fst snd] in E. injection E as E1 E2. subst k'.
  exists q. split; [exact Hq | exact E1].
Qed.

Lemma pd_user_blocks_in : forall L A q k, In (q, k) (user_blocks A) -> In (ptr_addr L q, k) (blocks L A).
Proof. intros L A q k H. unfold blocks. apply in_map_iff. exists (q, k). split; [reflexivity | exact H]. Qed.

Lemma pd_blk_range : forall L A mem md p k, aa_MR API L A mem md -> In (p, k) (blocks L A) ->
  4096 <= p /\ p + k <= YM05.alloc_ceiling.
Proof.
  intros L A mem md p k HM Hin. destruct (pd_blocks_user L A p k Hin) as (q & Hq & <-).
  exact (mr_blocks_range _ _ (aa_laws API) L A mem md q k HM Hq).
Qed.

Lemma pd_pairwise_mid : forall {T} (R : T -> T -> Prop) b1 z b2, YO0f.pairwise R (b1 ++ z :: b2) ->
  (forall y, In y (b1 ++ b2) -> R z y \/ R y z).
Proof.
  intros T R b1; induction b1 as [|w t IH]; intros z b2 H y Hy; cbn in *.
  - destruct H as [H1 _]. left. apply H1, Hy.
  - destruct H as [H1 H2]. destruct Hy as [<-|Hy].
    + right. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH z b2 H2 y Hy).
Qed.

Lemma pd_old_new : forall L A L' A' m md b1 b2 r k, aa_MR API L' A' m md ->
  blocks L' A' = b1 ++ (r, k) :: b2 -> blocks L A = b1 ++ b2 ->
  forall a k', In (a, k') (blocks L A) -> a + k' <= r \/ r + k <= a.
Proof.
  intros L A L' A' m md b1 b2 r k HM Hbl' Hbl a k' Hin.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L' A' m md HM) as Hd. rewrite Hbl' in Hd.
  rewrite Hbl in Hin. destruct (pd_pairwise_mid _ b1 (r, k) b2 Hd _ Hin) as [D|D];
    unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
Qed.

Lemma pd_mid_shrink : forall K sp L A mem md (E E' : Z -> Prop) L' A' mem' md',
  kb_mid B API K sp L A mem md E L' A' mem' md' ->
  (forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> E a -> E' a) ->
  kb_mid B API K sp L A mem md E' L' A' mem' md'.
Proof.
  intros K sp L A mem md E E' L' A' mem' md' (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10) HE.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H7|]. split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho Ho' Hs He. apply H8; [exact Ha | exact Ho | exact Ho' | exact Hs |].
  intros Hx. exact (He (HE a Ha Hx)).
Qed.

Lemma pd_present_of_wview : forall m (z : word), wview (ms_segs B) m z <> None -> ~ in_img B (bv_unsigned z) ->
  m z <> None.
Proof.
  intros m z Hw Hi E. apply Hw. unfold wview. rewrite E.
  destruct (find_segment (ms_segs B) (bv_unsigned z) 1) as [seg|] eqn:Hf; [|reflexivity].
  exfalso. exact (Hi (pd_seg_in_img _ seg Hf)).
Qed.

Theorem padded_holds : forall fx : YK11.FPState, @padded_contract fx rc B API F.
Proof.
  intros fx. unfold padded_contract.
  intros L A regs mem md b d n fill x Hpre Hro R10 R11 R12 Hfill Hlen Hn Hx Hxblk Hres Hroom.
  pose proof pd_img as HIL.
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htp & Herr & Haux).
  pose proof YM05.alloc_ceiling_value as Hceil. pose proof YM05.alloc_ceiling_lt as Hclt.
  assert (HPK : PADDED_K = 8240) by reflexivity.
  rewrite HPK in Hspc, Hstk.
  set (SP := spZ regs) in *.
  assert (ES : bv_unsigned (YK11.getr regs 2) = SP) by reflexivity.
  assert (Hsp : YK11.getr regs 2 = Z_to_bv 64 SP) by (unfold SP, spZ; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bytes_at_bound _ mem d x Hx) as Hxb. rewrite Hlen in Hxb.
  assert (Hxl : length x = Z.to_nat n) by lia.
  assert (Hro' : ro_agree rsegs mem) by (rewrite <- HS; exact Hro).
  destruct (kb_md B API L A mem md HMR) as (Hh & Hz).
  (* the 40 bytes of saved registers, part of the frame *)
  assert (PS : forall i, 0 <= i < 40 -> present mem (SP - 40 + i)).
  { intros i Hi. apply (pd_present_of_writable mem (SP - 40 + i)); [lia | | apply Hstk; lia].
    intros Hi'. pose proof (proj1 HIL _ Hi'). lia. }
  destruct (pd_rw_of_present mem (SP - 40) 40 ltac:(lia) ltac:(lia) ltac:(lia) PS) as (j & RWJ).
  assert (Hcond : forall z, 0 <= z < YM05.alloc_ceiling ->
      (owned B L A z \/ exists p k, In (p, k) (blocks L A) /\ p <= z < p + k) ->
      Frame.outside [(SP + -40, SP)] z) by (intros z Hz' _; cbn [Frame.outside]; split; [lia | exact I]).
  assert (Hwmk : forall a, (SP - 8240 <= a < SP) \/ (errno_addr B <= a < errno_addr B + 4) ->
      writable_at (ms_segs B) mem a) by (intros a [Ha|Ha]; [apply Hstk; exact Ha | apply Herr; exact Ha]).
  (* 0x1448c .. 0x144b4: the prologue, to malloc(n + 16) *)
  apply (kb_run B regs (Z_to_bv 64 PADDED) mem md
    (fun R pc' m' => pd0_post (YK11.getr regs 1) (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4)
       (YK11.getr regs 8) (YK11.getr regs 9) (YK11.getr regs 18) (YK11.getr regs 19) (YK11.getr regs 20)
       (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24) (YK11.getr regs 25)
       (YK11.getr regs 26) (YK11.getr regs 27) (@fp_regs fx) (@fp_csr fx) mem d n fill
       (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    _ Hh Hz).
  { rewrite HS. unfold rmk. rewrite R10, R11, R12. unfold PADDED.
    eapply evt_mono.
    - apply pd_seg0 with (j := j); [lia | rewrite ES; lia |].
      rewrite ES. replace (SP + -40) with (SP - 40) by lia. exact RWJ.
    - intros ms PO. pose proof PO as PO'. unfold pd0_post in PO'.
      destruct PO' as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & _).
      subst ms. do 3 eexists. split; [reflexivity | exact PO]. }
  intros R pc1 m1 regs1 HQ Hg1. cbv beta in HQ. unfold pd0_post in HQ.
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & E & MU1 & WM1 & RW1).
  pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
  cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM. subst R pc1 m1. clear E.
  rewrite ES in MU1, RW1.
  assert (WM1' : wmono (ms_segs B) mem m'') by (rewrite HS; exact WM1).
  assert (Hro1 : ro_agree (ms_segs B) m'').
  { rewrite HS. apply (pd_ro_agree_munch [(SP + -40, SP)] mem m'' Hro' MU1).
    intros a Ha Ho Hi. destruct (kb_outside_dec [(SP + -40, SP)] a) as [Hx'|Hx']; [exact (Ho Hx')|].
    pose proof (proj1 HIL a Hi). apply Hx'. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (BY1 : bytes_at rsegs m'' (SP + -40)
      (le8 (YK11.getr regs 19) ++ le8 (YK11.getr regs 18) ++ le8 (YK11.getr regs 9) ++ le8 (YK11.getr regs 8) ++
       le8 (YK11.getr regs 1))).
  { destruct RW1 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  clear RW1.
  assert (Hout1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + -40 <= a < SP) ->
      mbyte (ms_segs B) m'' a = mbyte (ms_segs B) mem a).
  { intros a Ha Hn'. apply (KindBGlue.mbyte_munch (ms_segs B) _ mem m'' a MU1 Ha).
    cbn [Frame.outside]. split; [exact Hn' | exact I]. }
  assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x144b8) by (rewrite Hg1; reflexivity).
  assert (G2 : YK11.getr regs1 2 = Z_to_bv 64 (SP + -48)) by (rewrite Hg1, ES; reflexivity).
  assert (G3 : YK11.getr regs1 3 = YK11.getr regs 3) by (rewrite Hg1; reflexivity).
  assert (G4 : YK11.getr regs1 4 = YK11.getr regs 4) by (rewrite Hg1; reflexivity).
  assert (G8 : YK11.getr regs1 8 = YK11.getr regs 8) by (rewrite Hg1; reflexivity).
  assert (G9 : YK11.getr regs1 9 = Z_to_bv 64 fill) by (rewrite Hg1; reflexivity).
  assert (G10 : YK11.getr regs1 10 = Z_to_bv 64 (n + 16)) by (rewrite Hg1; reflexivity).
  assert (G18 : YK11.getr regs1 18 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (G19 : YK11.getr regs1 19 = Z_to_bv 64 d) by (rewrite Hg1; reflexivity).
  assert (Hs1 : spZ regs1 = SP - 48) by (unfold spZ; rewrite G2, unsigned_lit by lia; lia).
  (* the malloc call *)
  rewrite <- HMAL.
  eapply SR_bind; [apply (MALLOC fx L A regs1 m'' md (n + 16) b) |].
  { apply (proj2 (call_pre_k_alloc B MR L A regs1 m'' md)).
    eapply (kb_pre_A B API PADDED_K 48 ALLOC_STACK L A regs mem md regs1 m'');
      [exact Hpre | lia | unfold ALLOC_STACK; lia | rewrite HPK; unfold ALLOC_STACK; lia | rewrite Hs1; reflexivity
      | | rewrite G4; reflexivity | | exact MU1 | exact WM1' | | exact Hcond].
    - rewrite Hs1. replace (SP - 48) with (SP + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
    - rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
    - intros z Hz' Hs. cbn [Frame.outside]. split; [lia | exact I]. }
  { exact Hro1. }
  { exact G10. }
  { exact Hres. }
  { exact Hroom. }
  intros c2 Hc2.
  destruct Hc2 as (L' & A' & regs2 & m2 & md' & q & -> & CP & R10q & Hq0 & Hq16 & FB & BL & BK & Hro2 & GK2 & SURV &
                   INIT & LEN & RES').
  pose proof CP as (HMR2 & HWF2 & Hbd2 & Hle2 & Hptr2 & RP2 & (vm' & Emd) & Hfr2 & Hblk2 & Hscr2).
  destruct FB as (Hq4096 & Hqc & Hqimg).
  destruct BL as (b1 & b2 & Hbl' & Hbl).
  assert (Hnb : In (q, n + 16) (blocks L' A')) by (rewrite Hbl'; apply in_or_app; right; left; reflexivity).
  destruct (pd_blocks_user L' A' _ _ Hnb) as (pq & Hpq & Epq).
  assert (Hpres : forall i, 0 <= i < n + 16 -> present m2 (q + i) /\ ~ owned B L' A' (q + i)).
  { intros i Hi. destruct (mr_blocks _ _ (aa_laws API) L' A' m2 md' pq (n + 16) i HMR2 Hpq Hi) as (P1 & _ & _ & P4).
    rewrite Epq in P1, P4. split; assumption. }
  assert (Hold : forall a k, In (a, k) (blocks L A) -> a + k <= q \/ q + (n + 16) <= a)
    by exact (pd_old_new L A L' A' m2 md' b1 b2 q (n + 16) HMR2 Hbl' Hbl).
  (* the frame bytes survive the call: they are above its stack window *)
  assert (Hfs : forall a, SP + -40 <= a < SP ->
      mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m'' a).
  { intros a Ha. refine (proj1 (Hfr2 a _ _ _ _ _)).
    - left. lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A m'' md a (kb_MR_A B API L A mem m'' md _ HMR MU1 Hcond) Ho).
      lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L' A' m2 md' a HMR2 Ho). lia.
    - unfold scratch_k. rewrite Hs1. unfold ALLOC_STACK. lia.
    - intros []. }
  assert (BY2 : bytes_at rsegs m2 (SP + -40)
      (le8 (YK11.getr regs 19) ++ le8 (YK11.getr regs 18) ++ le8 (YK11.getr regs 9) ++ le8 (YK11.getr regs 8) ++
       le8 (YK11.getr regs 1))).
  { rewrite <- HS. rewrite <- HS in BY1. apply (pd_bytes_frame m'' m2 _ _ BY1). intros i Hi.
    rewrite !length_app, !Mem.length_le8 in Hi. apply Hfs. lia. }
  (* the text survives the prologue and the call *)
  assert (Hxe : x = [] \/ x <> []) by (destruct x; [left; reflexivity | right; discriminate]).
  assert (BX2 : bytes_at rsegs m2 d x).
  { rewrite <- HS. destruct Hxe as [Hxe|Hxe].
    - rewrite Hxe. apply bytes_at_nil. lia.
    - destruct (Hxblk Hxe) as (a & k & Hin & Ha & Hk).
      apply (pd_bytes_frame mem m2 d _ Hx). intros i Hi. rewrite Hlen in Hi.
      pose proof (pd_blk_range L A mem md a k HMR Hin) as Hr.
      replace (d + i) with (a + (d + i - a)) by lia.
      rewrite (BK a k (d + i - a) Hin ltac:(intros []) ltac:(lia)).
      apply Hout1; lia. }
  assert (DS : n = 0 \/ d + n <= q \/ q + n + 16 <= d).
  { destruct Hxe as [Hxe|Hxe]; [left; rewrite Hxe in Hlen; cbn [length] in Hlen; lia | right].
    destruct (Hxblk Hxe) as (a & k & Hin & Ha & Hk). pose proof (Hold a k Hin). lia. }
  pose proof (proj1 (kb_mid_call B API _ L A regs1 m'' md _ L' A' regs2 m2 md' CP)) as MID2.
  assert (G2_1 : YK11.getr regs2 2 = Z_to_bv 64 (SP + -48)) by (rewrite <- G2; apply (RP2 2); unfold callee_saved; lia).
  assert (G2_9 : YK11.getr regs2 9 = Z_to_bv 64 fill) by (rewrite <- G9; apply (RP2 9); unfold callee_saved; lia).
  assert (G2_18 : YK11.getr regs2 18 = Z_to_bv 64 n) by (rewrite <- G18; apply (RP2 18); unfold callee_saved; lia).
  assert (G2_19 : YK11.getr regs2 19 = Z_to_bv 64 d) by (rewrite <- G19; apply (RP2 19); unfold callee_saved; lia).
  rewrite G1.
  destruct (kb_md B API L' A' m2 md' HMR2) as (Hh2 & Hz2).
  assert (Hro2r : ro_agree rsegs m2) by (rewrite <- HS; exact Hro2).
  assert (HRW : exists junk, rw_cells rsegs (normalize rsegs m2) q [CB (Z.to_nat (n + 16)) junk]).
  { apply pd_rw_of_present; [lia | lia | lia |]. intros i Hi. destruct (Hpres i Hi) as (Hp & _).
    apply pd_present_norm; [lia | exact (Hqimg i Hi) | exact Hp]. }
  destruct HRW as (junk & HRW).
  (* 0x144b8 .. 0x14518: the copy, the fill, the return *)
  apply (pd_run_n fx regs2 (Z_to_bv 64 0x144b8) m2 md'
    (fun R pc' m' => pd1_post (YK11.getr regs 1) (YK11.getr regs2 3) (YK11.getr regs2 4) (YK11.getr regs 8)
       (YK11.getr regs 9) (YK11.getr regs 18) (YK11.getr regs 19) (YK11.getr regs2 20) (YK11.getr regs2 21)
       (YK11.getr regs2 22) (YK11.getr regs2 23) (YK11.getr regs2 24) (YK11.getr regs2 25) (YK11.getr regs2 26)
       (YK11.getr regs2 27) (@fp_regs fx) (@fp_csr fx) (normalize rsegs m2) SP q n x fill
       (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    _ Hh2 Hz2 Hro2).
  { rewrite HS. unfold rmk. rewrite G2_1, R10q, G2_9, G2_18, G2_19.
    eapply evt_mono.
    - apply (pd_seg1 MEMCPY MEMSET) with (junk := junk);
        first [ exact Hxl | exact HRW | exact DS | apply mem_inv_normalize
              | apply bytes_at_normalize; [exact Hro2r | first [exact BX2 | exact BY2]] | lia ].
    - intros ms PO. pose proof PO as PO'. unfold pd1_post in PO'.
      destruct PO' as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m' & E & _).
      subst ms. do 3 eexists. split; [reflexivity | exact PO]. }
  intros R pc3 m0 m3 regs3 HK3 HREL HRS Hg3.
  cbv beta in HK3. unfold pd1_post in HK3.
  destruct HK3 as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m4 & E & MU3 & WM3 & _ & BQ).
  pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
  cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM. subst R pc3 m0. clear E.
  rewrite <- HS in MU3, WM3, BQ.
  destruct (pd_back m2 m3 m4 _ Hro2 HREL HRS MU3 WM3) as (MU3' & WM3' & Hro3).
  apply (proj2 (bytes_at_rel _ _ _ _ _ HREL)) in BQ.
  assert (Hin3 : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n + 16) ->
      mbyte (ms_segs B) m3 a = mbyte (ms_segs B) m2 a).
  { intros a Ha Hn'. apply (KindBGlue.mbyte_munch (ms_segs B) _ m2 m3 a MU3' Ha).
    cbn [Frame.outside]. split; [exact Hn' | exact I]. }
  assert (HP3 : forall z, m2 z <> None -> m3 z <> None).
  { intros z Hz'. destruct (kb_outside_dec [(q, q + n + 16)] (bv_unsigned z)) as [Ho|Ho].
    - rewrite (MU3' z Ho). exact Hz'.
    - apply pd_present_of_wview.
      + apply WM3'. unfold wview. destruct (m2 z) as [b0|] eqn:Ez; [discriminate | congruence].
      + assert (Hzr : q <= bv_unsigned z < q + n + 16).
        { cbn [Frame.outside] in Ho. pose proof (bv_unsigned_in_range 64 z) as Hr.
          destruct (Z_le_gt_dec q (bv_unsigned z)); destruct (Z_lt_ge_dec (bv_unsigned z) (q + n + 16));
            first [lia | exfalso; apply Ho; split; [lia | exact I]]. }
        replace (bv_unsigned z) with (q + (bv_unsigned z - q)) by lia. apply Hqimg. lia. }
  rewrite (kb_ret_pc _ Hra).
  apply SR_ret. split.
  - exists L', A', regs3, m3, md', q.
    split; [reflexivity|].
    split.
    { apply (kb_post B API).
      - apply (pd_mid_shrink _ _ _ _ _ _ (fun a => (False \/ False) \/ (q <= a < q + n + 16))).
        + eapply (kb_mid_tail B API HIL).
          * eapply (kb_mid_seqAX B API).
            -- eapply (kb_mid_A B API HIL); [exact HMR | exact HWF | exact Hbd | exact Hwmk | exact MU1 | exact WM1' | |
                 exact Hcond].
               intros z Hz' Hs He. cbn [Frame.outside]. split; [lia | exact I].
            -- exact MID2.
            -- rewrite Hs1. unfold ALLOC_STACK. lia.
            -- rewrite Hs1. lia.
            -- lia.
            -- lia.
            -- intros a _ _ [].
          * exact MU3'.
          * exact WM3'.
          * exact HP3.
          * intros z Hz' Hs He. cbn [Frame.outside]. split; [exact He | exact I].
          * intros z Hz' Ho. cbn [Frame.outside]. split; [|exact I]. intros Hb.
            apply (proj2 (Hpres (z - q) ltac:(lia))). replace (q + (z - q)) with z by lia. exact Ho.
          * intros p k i Hp _ Hi. pose proof (Hold _ _ (pd_user_blocks_in L A p k Hp)).
            cbn [Frame.outside]. split; [lia | exact I].
        + intros a Ha [[[]|[]]|Hb]. exfalso. destruct Ha as [Ha|Ha]; [lia|].
          apply (Hqimg (a - q)); [lia|]. replace (q + (a - q)) with a by lia. exact Ha.
      - pd_cs ltac:(rewrite Hg3; first
          [ reflexivity
          | exact (eq_sym Hsp)
          | match goal with |- YK11.getr _ (Z_to_bv 5 ?k) = _ =>
              transitivity (YK11.getr regs2 (Z_to_bv 5 k)); [reflexivity|];
              rewrite (RP2 k ltac:(unfold callee_saved; lia)), Hg1; reflexivity end ]). }
    split; [rewrite Hg3; reflexivity|].
    split; [exact Hq0|]. split; [exact Hq16|].
    split; [split; [exact Hq4096 | split; [exact Hqc | exact Hqimg]]|].
    split; [exists b1, b2; split; [exact Hbl' | exact Hbl]|].
    split.
    { intros a k i Hin _ Hi. pose proof (Hold a k Hin). pose proof (pd_blk_range L A mem md a k HMR Hin).
      rewrite (Hin3 (a + i) ltac:(lia) ltac:(lia)), (BK a k i Hin ltac:(intros []) Hi). apply Hout1; lia. }
    split; [exact Hro3|].
    split.
    { intros i Hi. assert (Ho : owned B L' A' (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
      assert (Ho0 : owned B L A (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
      assert (Hn' : ~ (q <= ms_got_guard B + i < q + n + 16)).
      { intros Hx'. apply (proj2 (Hpres (ms_got_guard B + i - q) ltac:(lia))).
        replace (q + (ms_got_guard B + i - q)) with (ms_got_guard B + i) by lia. exact Ho. }
      pose proof (mr_owned_low _ _ (aa_laws API) L' A' m2 md' _ HMR2 Ho) as Hlo.
      rewrite (Hin3 (ms_got_guard B + i) ltac:(lia) Hn'), (GK2 i Hi). apply Hout1; lia. }
    split; [exact SURV|]. split; [exact INIT|]. split; [exact LEN|]. exact RES'.
  - exists (@YK11.mkst fx regs3 (YK11.getr regs 1) m3 (YK11.seg_rom (ms_segs B))), md'.
    split; [reflexivity|].
    assert (Q10 : YK11.getr regs3 10 = Z_to_bv 64 q) by (rewrite Hg3; reflexivity).
    cbn [ms_mem ms_regs YK11.mkst]. rewrite Q10, unsigned_lit by lia. exact BQ.
Qed.

End PD.
