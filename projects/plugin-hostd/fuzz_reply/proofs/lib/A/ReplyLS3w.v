(* The count half of LS v3, part 6: the exit's count post and a long-input witness (a Theorem Labs lane's FREE-PIECES row B1c,
   a Theorem Labs lane).  proves no function (kind: invariant lemma).

   1. The exit's count post (a Theorem Labs lane 23:56Z).  The blocks one call leaves live are the next call's entry blocks, so the
      exit must give back the entry's count bound: xcnt_pre (ReplyLS3c.v) bounds the entry's blocks other than the
      input, the kept table and g_out.  xcnt_post is the same bound at any (ly, S); xcnt_pre is xcnt_post at the
      entry's (c_ly, c_S) (xcnt_pre_post).  fr_LS3c_exit_cnt: at the premises of LS_exit_end (the model rule of
      lib/A/W_LLVMFuzzerTestOneInput_exit_x.v:158-167 at a working branch bb9dae5d905: LS at S3 with
      ablocks S3 ~ input ++ model ++ rest, and ablocks S' ~ input ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest,
      the same rest), xcnt_post holds at S' with T0 := lm_G m: what S' holds besides the input, the table and g_out is
      fr_LS3's rest, and fr_CNT bounds the rest.  The one added premise is the block law's address bound (every live
      block's address is >= 4096), which gives lm_G m <> 0, so the table is the xcnt form's [(T0, ATABLE)]; the exit
      arm has it at S' as exit_x.v:360-362 lxk_blk_x (from the laws' alx_blocks; the cf law AR_blocks_law_cf,
      Reusable/YG0dcf.v:620).  fr_LS3c_exit_cnt_ret: the same at the returned state stack_free_state 1 fpos S' (it
      keeps the chunks).
   2. A long-input witness (a Theorem Labs lane's acceptance for the room round: an input of >= 72,687 BEGIN lines).  One open
      source (slot 0, the first head's) whose relay entry holds 72,687 keys of 22, 23 and 24 bytes (24,229 of each; a
      key block is its text and the NUL, 23..25 bytes), its 16,384-byte line buffer and its key-pointer array of
      8 * 72,688 = 581,504 bytes; the table; the source's partial buffer; no out buffer.  The 72,687 lines carry
      1,671,801 key bytes and 72,687 newlines = 1,744,488 bytes, which 27 writes of at most 65,535 bytes carry
      (t = 27); the input is those bytes and 4 header bytes per write (op, source, two length bytes:
      W_LLVMFuzzerTestOneInput_write.v:178-187), 1,744,596 bytes, all consumed.  The allocator state holds exactly the
      input block and the model's blocks (ablocks = input ++ model ++ [], as ReplyLS3.v sat3 builds ls3_S from chunks;
      the 72,687 key chunks come from a Fixpoint), and the call's entry state holds only the input block.
      w_fr_LS3c proves fr_LS3c there; w_sec_cut evaluates ReplyLSCntM.fr_LS3c_sec_cut (106); w_counts computes the
      state's counts (secondary 2, class 2: 72,687, classes 18, 24, 27: 1 each, cnt24 = 1); w_classes names each
      block's class.  Every computed fact is a
      vm-checked equation (assert (E : f x = v) by (vm_compute; reflexivity)).  The key texts are distinct by
      construction (three index bytes) and NUL-free; the witness proves fr_LS3c only (not RINV or amodel_at). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3 ReplyLSCntL ReplyLS3c ReplyLSCntM.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== 1. the exit's count post *)
Section xpost.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* xcnt_pre's bound at a state (ly, S): the blocks of S other than the input, the kept table (when T0 <> 0) and g_out *)
Definition xcnt_post (cx : lfcx) (ly : alayout) (S : astate) (T0 cap out : Z) : Prop :=
  cnt_sec (ablocks B ly S) - cnt_sec (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++
    aout_blks cap out) <= SEC0 /\
  forall c, cnt_cls c (ablocks B ly S) - cnt_cls c (input_blks cx ++
    (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out) <= CLS0.

(* the entry's bound is the post's form at the entry's state *)
Lemma xcnt_pre_post : forall cx T0 cap out,
  xcnt_pre B cx T0 cap out <-> xcnt_post cx (c_ly cx) (c_S cx) T0 cap out.
Proof. intros cx T0 cap out. unfold xcnt_pre, xcnt_post. split; intros H; exact H. Qed.

(* the exit: S' holds the input, the table, g_out and fr_LS3's rest; fr_CNT bounds the rest *)
Lemma fr_LS3c_exit_cnt : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  fr_LS3c B cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p) ->
  xcnt_post cx ly' S' (lm_G m) cap out.
Proof.
  intros cx t m ly3 S3 rest ly' S' cap out (_ & (C1 & C2 & _)) HP3 HP' HA.
  assert (HG : (lm_G m =? 0) = false).
  { apply Z.eqb_neq. intros E.
    assert (Hin : In (lm_G m, ATABLE) (ablocks B ly' S')).
    { apply (Permutation_in _ (Permutation_sym HP')). apply in_or_app. right. left. reflexivity. }
    pose proof (HA _ _ Hin). lia. }
  unfold xcnt_post. rewrite HG. cbv beta iota. split.
  - rewrite (cnt_sec_perm _ _ HP3), !cnt_sec_app in C1.
    rewrite (cnt_sec_perm _ _ HP').
    repeat progress rewrite ?cnt_sec_app, ?cnt_sec_cons, ?cnt_sec_nil. lia.
  - intros c. specialize (C2 c).
    rewrite (cnt_cls_perm _ _ _ HP3), !cnt_cls_app in C2.
    rewrite (cnt_cls_perm _ _ _ HP').
    repeat progress rewrite ?cnt_cls_app, ?cnt_cls_cons, ?cnt_cls_nil. lia.
Qed.

(* the same at the state the call returns (stack_free_state keeps the chunks) *)
Lemma fr_LS3c_exit_cnt_ret : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) fpos cap out,
  fr_LS3c B cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p) ->
  xcnt_post cx ly' (stack_free_state 1 fpos S') (lm_G m) cap out.
Proof.
  intros cx t m ly3 S3 rest ly' S' fpos cap out H HP3 HP' HA.
  assert (E : ablocks B ly' (stack_free_state 1 fpos S') = ablocks B ly' S') by reflexivity.
  unfold xcnt_post. rewrite E. exact (fr_LS3c_exit_cnt cx t m ly3 S3 rest ly' S' cap out H HP3 HP' HA).
Qed.
End xpost.

(* ================================================================== 2. the long-input witness *)
(* a block list's equality, decided (the vm checks it) *)
Fixpoint zz_eqb (l1 l2 : list (Z * Z)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (a, b) :: t1, (c, d) :: t2 => (a =? c) && (b =? d) && zz_eqb t1 t2
  | _, _ => false
  end.
Lemma zz_eqb_eq : forall l1 l2, zz_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|[a b] t1 IH]; intros [|[c d] t2] H; cbn [zz_eqb] in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as (H1 & H2). apply andb_true_iff in H1 as (H1 & H3).
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H3. subst c d. f_equal. exact (IH t2 H2).
Qed.

Definition W_NK : Z := 72687.                (* the held keys (BEGIN lines) *)
Definition W_T : Z := 27.                    (* the write operations *)
Definition W_KH : Z := 8 * 72688.            (* the key-pointer array: 581,504 bytes *)
Definition W_N : Z := 1744488 + 4 * W_T.     (* the input: 1,744,488 line bytes, 4 header bytes per write *)
(* key i: 22 + i mod 3 bytes of text *)
Definition w_klen (i : Z) : Z := 22 + i mod 3.
Definition w_ktext (i : Z) : list byte :=
  repeat (Z_to_bv 8 107) (Z.to_nat (w_klen i - 3)) ++
  [Z_to_bv 8 (1 + i mod 255); Z_to_bv 8 (1 + i / 255 mod 255); Z_to_bv 8 (1 + i / 65025 mod 255)].
(* the chunks: the input and the key-pointer array are secondary requests, the rest primary *)
Definition w_kin : YG00.chunk := YG00.mkChunk (YG00.PSec 0 (2 ^ 40)) W_N YG00.CAllocated.
Definition w_ktab : YG00.chunk := YG00.mkChunk (YG00.PPrim (2 ^ 32)) ATABLE YG00.CAllocated.
Definition w_kbuf : YG00.chunk := YG00.mkChunk (YG00.PPrim (2 * 2 ^ 32)) E_ENT YG00.CAllocated.
Definition w_khp : YG00.chunk := YG00.mkChunk (YG00.PSec 1 (2 ^ 41)) W_KH YG00.CAllocated.
Definition w_kpart : YG00.chunk := YG00.mkChunk (YG00.PPrim (3 * 2 ^ 32)) APARTIAL YG00.CAllocated.
Definition w_kch (i : Z) : YG00.chunk := YG00.mkChunk (YG00.PPrim (4 * 2 ^ 32 + 64 * i)) (w_klen i + 1) YG00.CAllocated.
Fixpoint w_kchs (n : nat) (i : Z) : list YG00.chunk :=
  match n with O => [] | S n' => w_kch i :: w_kchs n' (i + 1) end.
(* the allocator states: at the call's entry only the input block; at the witness the input and the model's blocks *)
Definition w_S0 : astate := YG00.set_chunks [w_kin] YG00.init_state.
Definition w_S : astate :=
  YG00.set_chunks ([w_kin; w_ktab; w_kbuf; w_khp] ++ w_kchs (Z.to_nat W_NK) 0 ++ [w_kpart]) YG00.init_state.

Section wit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition w_addr (k : YG00.chunk) : Z := sptr_addr B ls3_ly (YG00.ck_user k).
Fixpoint w_keys (n : nat) (i : Z) : list (Z * list byte * list byte) :=
  match n with O => [] | S n' => (w_addr (w_kch i), w_ktext i, []) :: w_keys n' (i + 1) end.
(* the relay entry of the open source (fd 100): its line buffer at 16,384, the key-pointer array, the keys; no
   unfinished line *)
Definition w_e : rentry :=
  RE 100 0 0 (repeat (Z_to_bv 8 0) 4) (w_addr w_kbuf) 0 E_ENT (w_addr w_khp) W_KH (repeat (Z_to_bv 8 0) 4)
     (w_keys (Z.to_nat W_NK) 0) [] (repeat (Z_to_bv 8 0) (Z.to_nat E_ENT)).
(* the open source: the first head's (its lists empty, its partial buffer) *)
Definition w_h : hsrc := oa_new_src 100 (w_addr w_kpart) (repeat (Z_to_bv 8 0) (Z.to_nat APARTIAL)).
Definition w_m : lmod := LM W_N [Some w_h; None; None; None] (w_addr w_ktab) [w_e] (CTL 3 0 0 0 0) [] 0 0 0 0 1.
Definition w_cx : lfcx (rc := rc) :=
  LFCX ls3_ly w_S0 ls3_W bvmap_empty (fun _ => None) ls3_md (w_addr w_kin) W_N [] 0.

(* the witness's shape *)
Lemma w_shape :
  lm_es w_m = [w_e] /\ nopen (lm_hs w_m) = 1 /\ re_nheld w_e = W_NK /\ re_kh w_e = W_KH /\ re_cap w_e = E_ENT /\
  Forall (fun k => 22 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= 24) (re_keys w_e) /\
  c_n w_cx = W_N /\ lm_k w_m = W_N /\ lm_cap w_m = 0.
Proof.
  assert (E1 : nopen (lm_hs w_m) = 1) by (vm_compute; reflexivity).
  assert (E2 : re_nheld w_e = W_NK) by (vm_compute; reflexivity).
  assert (F : forallb (fun k => (22 <=? Z.of_nat (length (gestures_end_b_c.key_text k))) &&
                                (Z.of_nat (length (gestures_end_b_c.key_text k)) <=? 24)) (re_keys w_e) = true)
    by (vm_compute; reflexivity).
  refine (conj eq_refl (conj E1 (conj E2 (conj eq_refl (conj eq_refl (conj _ (conj eq_refl (conj eq_refl eq_refl)))))))).
  apply Forall_forall. intros k Hk. pose proof (proj1 (forallb_forall _ _) F k Hk) as Hb.
  apply andb_true_iff in Hb as (Hb1 & Hb2). apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. lia.
Qed.

(* the state's blocks are the input's and the model's, nothing else *)
Lemma w_EA : ablocks B ls3_ly w_S = input_blks w_cx ++ model_blks w_m ++ [].
Proof.
  apply zz_eqb_eq.
  assert (E : zz_eqb (ablocks B ls3_ly w_S) (input_blks w_cx ++ model_blks w_m ++ []) = true)
    by (vm_compute; reflexivity).
  exact E.
Qed.

(* fr_LS3c at the witness: rest [], e0 0; PHI3 = 2,349,272 (the model's bytes) + 4 * 1,671,801 (the held key bytes)
   + 256 (the source's two empty lists' credit) *)
Lemma w_fr_LS3c : fr_LS3c B w_cx W_T w_m ls3_ly w_S.
Proof.
  pose proof w_EA as EA.
  assert (Hbb : blocks_bytes w_S0 = W_N) by (vm_compute; reflexivity).
  assert (Hin : bsum (input_blks w_cx) = W_N) by (vm_compute; reflexivity).
  assert (HS : c_S w_cx = w_S0) by reflexivity.
  assert (Hn : c_n w_cx = W_N) by reflexivity.
  assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  assert (HL : LIVE_MAX = 17179869184) by reflexivity.
  assert (En : npend w_m = 0) by (vm_compute; reflexivity).
  assert (Ek : kk w_cx w_m = W_N) by (vm_compute; reflexivity).
  assert (Eo : nopen (lm_hs w_m) = 1) by (vm_compute; reflexivity).
  assert (Ep : PHI3 w_m = 9036732) by (vm_compute; reflexivity).
  assert (Hl : length (lm_hs w_m) = 4%nat) by reflexivity.
  split.
  - exists [], 0.
    assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
    rewrite EA, HS, Hbb, Hn, Hin, Hrest, HC, HL, En, Ek, Eo, Ep.
    split; [apply Permutation_refl|].
    unfold W_N, W_T, W_OPEN, MB_K, MB_C, ATABLE, APARTIAL, E_ENT, K0.
    refine (conj _ (conj _ (conj _ (conj Hl (conj _ _))))); lia.
  - unfold fr_CNT. rewrite EA, !cnt_sec_app, cnt_sec_nil.
    split; [unfold SEC0; lia | split; [| rewrite En; unfold W_T; lia]].
    intros c. rewrite !cnt_cls_app, cnt_cls_nil. unfold CLS0. lia.
Qed.

(* the model's size facts (ReplyCnt.msz_ok) *)
Lemma w_msz : msz_ok (lm_es w_m) (lm_hs w_m).
Proof.
  assert (F : forallb (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <=? APARTIAL) (re_keys w_e) = true)
    by (vm_compute; reflexivity).
  assert (Ec : re_cap w_e = E_ENT) by reflexivity.
  split.
  - constructor; [| constructor]. split; [rewrite Ec; unfold E_ENT; lia|].
    apply Forall_forall. intros k Hk. apply Z.leb_le. exact (proj1 (forallb_forall _ _) F k Hk).
  - constructor; [split; constructor | repeat constructor].
Qed.

(* the per-call secondary bound (ReplyLSCntM.fr_LS3c_sec_cut) at the witness: t + |es| + 3 |hs| + 2 + SEC0 = 106 *)
Lemma w_sec_cut : cnt_sec (ablocks B ls3_ly w_S) <= 106.
Proof.
  pose proof (fr_LS3c_sec_cut B w_cx W_T w_m ls3_ly w_S w_fr_LS3c w_msz) as H.
  assert (E1 : Z.of_nat (length (lm_es w_m)) = 1) by reflexivity.
  assert (E2 : Z.of_nat (length (lm_hs w_m)) = 4) by reflexivity.
  rewrite E1, E2 in H. unfold W_T, SEC0 in H. lia.
Qed.

(* the state's counts: secondary (the input and the key-pointer array), and each primary class 1..30 (class 2: the
   keys; 18: the table; 24: the partial buffer; 27: the line buffer) *)
Definition w_cnts (l : list (Z * Z)) : list Z := map (fun c => cnt_cls c l) (map Z.of_nat (seq 1 30)).
Lemma w_counts :
  cnt_sec (ablocks B ls3_ly w_S) = 2 /\ cnt24 (ablocks B ls3_ly w_S) = 1 /\
  cnt_cls 2 (ablocks B ls3_ly w_S) = 72687 /\
  w_cnts (ablocks B ls3_ly w_S) =
    [0; 72687; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0].
Proof.
  assert (E1 : cnt_sec (ablocks B ls3_ly w_S) = 2) by (vm_compute; reflexivity).
  assert (E2 : cnt24 (ablocks B ls3_ly w_S) = 1) by (vm_compute; reflexivity).
  assert (E3 : cnt_cls 2 (ablocks B ls3_ly w_S) = 72687) by (vm_compute; reflexivity).
  assert (E4 : w_cnts (ablocks B ls3_ly w_S) =
    [0; 72687; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0])
    by (vm_compute; reflexivity).
  exact (conj E1 (conj E2 (conj E3 E4))).
Qed.

(* which block is in which class: the input and the key-pointer array are secondary; a key block (23..25 bytes) is
   class 2, the table class 18, the partial buffer class 24 (K_BATCH_CLASS), the line buffer class 27 *)
Lemma w_classes :
  Psec W_N = true /\ Psec W_KH = true /\
  PresetRoom.cls 23 = Some 2 /\ PresetRoom.cls 24 = Some 2 /\ PresetRoom.cls 25 = Some 2 /\
  PresetRoom.cls ATABLE = Some 18 /\ PresetRoom.cls APARTIAL = Some 24 /\ PresetRoom.cls E_ENT = Some 27.
Proof.
  assert (E1 : Psec W_N = true) by (vm_compute; reflexivity).
  assert (E2 : Psec W_KH = true) by (vm_compute; reflexivity).
  assert (E3 : PresetRoom.cls 23 = Some 2) by (vm_compute; reflexivity).
  assert (E4 : PresetRoom.cls 24 = Some 2) by (vm_compute; reflexivity).
  assert (E5 : PresetRoom.cls 25 = Some 2) by (vm_compute; reflexivity).
  assert (E6 : PresetRoom.cls ATABLE = Some 18) by (vm_compute; reflexivity).
  assert (E7 : PresetRoom.cls APARTIAL = Some 24) by (vm_compute; reflexivity).
  assert (E8 : PresetRoom.cls E_ENT = Some 27) by (vm_compute; reflexivity).
  exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E6 (conj E7 E8))))))).
Qed.

(* the witness in one statement *)
Lemma fr_LS3c_sat_long : exists (cx : lfcx (rc := rc)) t m ly S,
  fr_LS3c B cx t m ly S /\ t = 27 /\ c_n cx = 1744596 /\
  (exists e, lm_es m = [e] /\ re_nheld e = 72687 /\ re_kh e = 8 * 72688 /\
     Forall (fun k => 22 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= 24) (re_keys e)) /\
  ablocks B ly S = input_blks cx ++ model_blks m ++ [] /\
  cnt_sec (ablocks B ly S) = 2 /\ cnt24 (ablocks B ly S) = 1 /\ cnt_cls 2 (ablocks B ly S) = 72687.
Proof.
  destruct w_shape as (S1 & _ & S3 & S4 & _ & S6 & S7 & _).
  destruct w_counts as (C1 & C2 & C3 & _).
  exists w_cx, W_T, w_m, ls3_ly, w_S.
  refine (conj w_fr_LS3c (conj eq_refl (conj S7 (conj _ (conj w_EA (conj C1 (conj C2 C3))))))).
  exists w_e. exact (conj S1 (conj S3 (conj S4 S6))).
Qed.
End wit.
