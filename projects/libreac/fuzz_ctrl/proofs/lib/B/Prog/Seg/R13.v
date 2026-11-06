(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 844 of its 926 lines of code are new or changed and 929 lines of the source are left out. *)
(* Segment R13 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): cut Inv_B81860_at b
   (v1.9 pc 0x81860) -> cut Inv_B81aa0_at b (v1.9 pc 0x81aa0) (plan-asan-ubsan.md section 2 (a working note, not in this delivery), row R13, range
   0x81860-0x818a4; S_R13 (forms-asan-ubsan.md (a working note, not in this delivery)); section 4, FREE = wrapper_free at 0x534b4). rule 24: no function
   proved (a slot segment).  Re-fit of the v1.8 proof (a working branch c439fa41c5b) onto the v1.9.0 bytes and
   a Theorem Labs lane's v1.9 cut bundle (pcs +0x64, frame 3136 bytes, the 33-conjunct RBE, CUR in s7 / s9, the constant 32 in s11).
   The cut 0x81860 is the return point of the reac_identity_ingest call 0x8185c (R11, b = 3, 4; R12, b = 6). From it
   the code runs four instructions and one call:
     0x81860 li a1,1 ; 0x81864 beq a0,a1,0x81a98 (taken: a0 = 1, the ingest result) ;
     0x81a98 mv a0,s4 ; 0x81a9c jal wrapper_free (a0 = s4 = Phi_r, the turn's buffer) -> 0x81aa0.
   The fall-through 0x81868 `j 0x82fa4` is the abort edge of plan section 1.5 row 11 (the R13 "check" 81804); it is
   not taken because a0 = 1. The other R13 "check" 8181c (row 12) and the rest of the plan range, 0x8186c-0x818a4,
   are the b = 0 arm of R10's dispatch (0x817c4 bgeu a1,a3,0x8186c): no edge from 0x81860 reaches them, and R10's
   lemma steps them (0x8187c beq a0,9 taken). So the segment has ONE exit, 0x81aa0, at every b. The run holds no
   instrumented shadow check, no UBSan trap branch and no store; there is no cut at 0x81a98, so the free call is
   this segment's (R20's FREE@0x81a9c is the same call on R20's own path).
   The call is taken on the frame's AsanAllocAPI law aa_free (afree_at at as_free = 0x534b4, never its code) from
   the a_call_pre that fra_call_pre builds from FRA + ENT (ret_ok from the jal: ra = 0x81aa0; K = AK_FREE = 4096 <=
   FN_STACK), with the live list hb1 Phi n ++ g_H g = [] ++ (Phi, n) :: g_H g (n = rnb g b). The post has the live
   list g_H g, which is the exit cut's hb = []. FRA moves by sl_mid, ENT by ent_call (the touched bytes are the
   freed block: app memory below stklo, off the image and off every entry block by a_laws_blocks /
   a_laws_disjoint). Every byte the exit reads is kept by a_call_post's frame clause: it is on the real stack at
   or above sp, in the frame (the real stack or the side stack FS), a shadow byte of a real-stack, FS or image
   byte, a musl client cell (the sink words), a RELRO byte of the image (frame_facts) or a byte of the image's
   read-only segment (a_laws_ro_not_owned: the row-name strings of RBE), none of which the allocator owns, and
   none of which is in the allocator's window [sp - 4096, sp), errno, the OOM flag or the freed block.
   RBE (adopt 9) at the exit: the thirty-three spills (the twenty-one of adopt 6, PRA's ten, [A+160] = fr + 64 and
   [A+112] = fr + 2256) are on the real stack above A >= sp; the shadow bytes of out[], our[], the identity record
   and (adopt 10) the fragment record fr + 2256 (72 bytes) are frame shadow; the row-name strings and the box bytes at BOXA lie in the image's
   read-only segment [0x21140, 0x218f0) (r13_rname, by computation on the 11 catalogue rows), and the row table at
   BA_FR + 72 and the catalogue row at mrow lie in RELRO's middle block, so these image bytes and their shadow bytes
   are kept. RBE has no thread-cell clause (adopt FSFREE; Seg/Tac_fsfree.v fra_rbe_tls gives it from FRA alone).
   FRA's input facts move across the call: for g_n > 0 the input block is a live block of g_H g apart from the freed
   block (a_laws_disjoint), so its bytes and its shadow bytes are the allocator's in neither state.

   No local cut: seg_R13 is proved against the official Inv_B81860_at (SlotInv.v, de2516edf5), whose body adds,
   inside the CUTST predicate,
     IDBr g fr (RID (g_in g) (S b)) m /\ FGBr g fr (RFG (g_in g) (S b)) m /\ rg regs 20 phi /\ a0v regs 1
   - a0v regs 1: the ingest result; 0x81864 beq a0,a1 with a1 = 1 decides the abort edge 0x81868;
   - rg regs 20 phi: s4 = Phi_r (0x8176c mv s4,a0), the block the free call releases (a0 = s4 at 0x81a98);
   - IDBr / FGBr at turn S b: Inv_B81aa0_at b names the records of turn S b (RB g fr b (RID (S b)) (RFG (S b))), and
     the free call keeps both records (frame bytes);
   - (adopt 10, a working branch de0ff9e12a) rg regs 27 32: s11 = 32, which the three instructions do not write and the free
     call keeps (a_callee_saved 27), so the exit Inv_B81aa0_at gets it. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcIdentModel RcFrag RcFragLib reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_cls.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module BAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module BAC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_as_c.
Module RS6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.

(* ---- the run 0x81860 .. 0x81a9c (4 instructions, ending at the allocator's free entry) ---- *)

(* A branch whose condition is a closed term (every register it reads holds a literal here). *)
Ltac r13_if_true :=
  first [ if_true
        | lazymatch goal with
          | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
              replace c with true; [cbv_concl_iota | symmetry; vm_compute; reflexivity]
          end ].

(* 0x81860 li a1,1; 0x81864 beq a0,a1,0x81a98 (taken: a0 = 1, so the abort edge 0x81868 is not reached);
   0x81a98 mv a0,s4; 0x81a9c jal wrapper_free. *)
Lemma r13_evt : forall (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                        : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 1 ->
  evt rsegs
    (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x534b4) fc None m (seg_rom rsegs) /\
       getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = s4 /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 27 = s11 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
       getr R 26 = s10)
    (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81860) fc None m (seg_rom rsegs)).
Proof.
  intros rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step; step; try r13_if_true.
  do 2 step.
  finish; try simp_regs; first [reflexivity | vm_compute; reflexivity].
Qed.

(* ---- register, cell and byte helpers (R7's) ---- *)

Lemma r13_mkR_of : forall regs,
  Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Bytes whose cells keep their contents. *)
Lemma r13_keep_bytes : forall m m' a bs,
  bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs m' x = mbyte rsegs m x) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). exact (HK (a + Z.of_nat i) ltac:(lia)).
Qed.

(* A buffer stays addressable when its shadow bytes keep their contents (ADDR-KEEP). *)
Lemma r13_addr_keep : forall m m' p n,
  addressable m p n ->
  (forall i, 0 <= i < n -> mbyte rsegs m' (shadow_addr (p + i)) = mbyte rsegs m (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) HK. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & bb & Hb & Hok).
  split; [exact Happ|]. exists bb. split; [|exact Hok]. rewrite <- Hb. exact (HK i Hi).
Qed.

(* A register value read twice in [0, 2^64). *)
Lemma r13_rg_eq : forall regs r x y, rg regs r x -> rg regs r y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y.
Proof.
  intros regs r x y Hx Hy Hxr Hyr. pose proof (rg_eq64 regs r x y Hx Hy) as Hm.
  rewrite !Z.mod_small in Hm by lia. exact Hm.
Qed.

(* A callee-saved register of an allocator entry, at a register named by a numeral. *)
Lemma r13_regs_kept_at : forall regs regs' (r : reg) (z : Z),
  AC.a_regs_kept regs regs' -> AC.a_callee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HK Hc <-. exact (HK z Hc). Qed.

(* The shadow byte of the frame's 8 k-th byte. *)
Lemma r13_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof.
  intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* ---- image placement, on the image's segment table ---- *)

(* The image's loaded segments all end below GT = 0x5fe000. *)
Lemma r13_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r13_img_range : forall x, AC.a_in_img x -> 0 <= x < 6283264.
Proof.
  intros x (s & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r13_img_top s Hin) as Hs. cbv beta in Hs.
  apply Z.leb_le in Hs. pose proof (N2Z.is_nonneg (seg_base s)). lia.
Qed.

Definition r13_img_cov (lo hi : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs.

Lemma r13_img_cov_in : forall lo hi x, r13_img_cov lo hi = true -> lo <= x < hi -> AC.a_in_img x.
Proof.
  intros lo hi x H Hx. unfold r13_img_cov in H. apply existsb_exists in H. destruct H as (s & Hin & Hb).
  apply andb_true_iff in Hb as (H1 & H2). apply Z.leb_le in H1, H2.
  exists s. split; [exact Hin | lia].
Qed.

(* The registered globals are image bytes; so are the musl sink cells. *)
Lemma r13_ag_cov : forallb (fun p => r13_img_cov (fst p) (fst p + snd p)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r13_ag_img : forall a, in_globals AF.frame_AG a -> AC.a_in_img a.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r13_ag_cov (lo, len) Hin) as H. cbn [fst snd] in H.
  exact (r13_img_cov_in _ _ _ H Hr).
Qed.

Lemma r13_sink_cov_a : r13_img_cov 0x5fc8e1 0x5fc8e2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r13_sink_cov_b : r13_img_cov 0x5fcd40 0x5fcd50 = true.
Proof. vm_compute. reflexivity. Qed.

(* The client objects of musl's stdio the sink words live in (Contract.v a_client). *)
Lemma r13_client_a : forall a, 0x5dc680 <= a < 0x5dc680 + 131728 -> AC.in_blocks AC.a_client a.
Proof. intros a Ha. exists 0x5dc680, 131728. split; [cbn; tauto | exact Ha]. Qed.
Lemma r13_client_b : forall a, 0x5fc918 <= a < 0x5fc918 + 4320 -> AC.in_blocks AC.a_client a.
Proof. intros a Ha. exists 0x5fc918, 4320. split; [cbn; tauto | exact Ha]. Qed.

(* The image's RELRO range is the one block [0x9f168, 0xa15e8) (v1.9.0 frame_RELRO); the row table (BA_FR + 72 ..
   + 240) and the catalogue row (mrow .. mrow + 296) lie in it. *)
Lemma r13_relro_range : forall a, in_globals AF.frame_RELRO a -> 0x9f168 <= a < 0xa15e8.
Proof.
  intros a (lo & len & Hin & Hr). unfold AF.frame_RELRO in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [inversion E; subst; lia|]); destruct Hin.
Qed.

Lemma r13_relro_in : forall x, 0x9f168 <= x < 0x9f168 + 9344 -> in_globals AF.frame_RELRO x.
Proof.
  intros x Hx. exists 0x9f168, 9344.
  split; [unfold AF.frame_RELRO; cbn [In]; left; reflexivity | lia].
Qed.

(* The row table ba_tbl is 168 bytes (7 rows of 24). *)
Lemma r13_tbl_len : Z.of_nat (length BAP.ba_tbl) = 168.
Proof. vm_compute. reflexivity. Qed.

(* The catalogue row mrow(in) lies at CAT + 296 * istar with istar in [0, 10], so in RELRO's middle block. *)
Lemma r13_mrow_range : forall inp, 0x9f620 <= mrow inp <= 0x9f620 + 296 * 10.
Proof.
  intros inp. unfold mrow, CAT, CAT_ROW.
  assert (Hi : 0 <= istar inp < CAT_N) by (unfold istar; apply Z.mod_pos_bound; unfold CAT_N; lia).
  unfold CAT_N in Hi. lia.
Qed.

(* The catalogue row rt_mb(in) is 296 bytes. *)
Lemma r13_mb_len : forall inp, length (rt_mb inp) = 296%nat.
Proof.
  intros inp. unfold rt_mb, rowb, img.
  destruct (Lib.Image.image_bytes rsegs (CAT + CAT_ROW * istar inp) 296) eqn:Ei;
    [exact (Lib.Image.image_bytes_length rsegs 296 _ _ Ei) | apply repeat_length].
Qed.

(* The image's first loaded segment [0x10000, 0x30104) is read-only; it holds the box bytes at BOXA = 0x21140 and
   the catalogue's row-name strings. *)
Definition r13_ro_cov (lo hi : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
                    (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs.

Lemma r13_ro_cov_ok : r13_ro_cov 0x21140 0x218f0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r13_ro_in : forall x, 0x21140 <= x < 0x218f0 -> AC.a_in_ro x.
Proof.
  intros x Hx. pose proof r13_ro_cov_ok as H. unfold r13_ro_cov in H.
  apply existsb_exists in H. destruct H as (s & Hin & Hb).
  apply andb_true_iff in Hb as (Hb & H2). apply andb_true_iff in Hb as (Hw & H1).
  apply negb_true_iff in Hw. apply Z.leb_le in H1, H2.
  exists s. split; [exact Hin|]. split; [exact Hw | lia].
Qed.

Lemma r13_ro_img : forall x, AC.a_in_ro x -> AC.a_in_img x.
Proof. intros x (s & Hin & _ & Hr). exists s. split; [exact Hin | exact Hr]. Qed.

(* The row name of every catalogue row that has one lies in [0x214a0, 0x218e0] (by computation on the 11 rows of
   BOX_CATALOGUE; rt_mb inp is row istar inp, istar inp < 11). *)
Lemma r13_rows_b :
  forallb (fun i => (RS6.has (rowb i) =? 0) || (RS6.rname (rowb i) =? 0) ||
                    ((0x214a0 <=? RS6.rname (rowb i)) && (RS6.rname (rowb i) <=? 0x218e0)))
    [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r13_rname : forall inp, RS6.has (rt_mb inp) <> 0 -> RS6.rname (rt_mb inp) <> 0 ->
  0x214a0 <= RS6.rname (rt_mb inp) <= 0x218e0.
Proof.
  intros inp H1 H2. unfold rt_mb in *.
  assert (Hi : 0 <= istar inp < 11) by (unfold istar, CAT_N; apply Z.mod_pos_bound; lia).
  assert (Hin : In (istar inp) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]) by (cbn [In]; lia).
  pose proof (proj1 (forallb_forall _ _) r13_rows_b _ Hin) as Hb. cbv beta in Hb.
  apply orb_true_iff in Hb as [Hb|Hb]; [apply orb_true_iff in Hb as [Hb|Hb]|].
  - apply Z.eqb_eq in Hb. contradiction.
  - apply Z.eqb_eq in Hb. contradiction.
  - apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1, Hb2. lia.
Qed.

(* The row-name string is at most 16 bytes. *)
Lemma r13_cstr_len : forall k a, (length (img_cstr a k) <= k)%nat.
Proof.
  induction k as [|k IH]; intros a; cbn [img_cstr]; [cbn [length]; lia|].
  match goal with |- context [if ?c then _ else _] => destruct c end; cbn [length];
    [lia | specialize (IH (a + 1)); lia].
Qed.

Lemma r13_nb_len : forall inp, (length (rt_nb inp) <= 16)%nat.
Proof. intros inp. unfold rt_nb. apply r13_cstr_len. Qed.

(* ---- the turn records: the identity record RID is 38 bytes and the fragment record RFG 72 bytes at every turn
   (R6's r6_rid_len / r6_rfg_len), so both lie inside the frame ---- *)

Lemma r13_rid_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst];
    first [exact IH | apply RcIdentModel.ING_length; exact IH].
Qed.

Lemma r13_rtg_len : forall inp x, length (rt_g inp x) = 50%nat.
Proof. intros inp x. unfold rt_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma r13_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|exact Hs].
  assert (Hn : 1 <= RcFrag.fg_n g <= 22).
  { unfold RcFrag.fg_fr in Efr.
    apply andb_prop in Efr as [Efr _]. apply andb_prop in Efr as [Efr H22]. apply andb_prop in Efr as [_ H1].
    apply Z.leb_le in H22. apply Z.leb_le in H1. lia. }
  destruct (RcFrag.bat g 19 =? 1).
  - cbn [fg_next]. unfold RcFrag.fg_first, RcFrag.fg_body, RcFrag.bsl.
    rewrite !length_app, !length_firstn, !length_skipn, Hs, Hg. cbn [length]. lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb].
    + assert (HT : RcFrag.fg_T st g <= 64).
      { unfold RcFrag.fg_keep in Ek. apply andb_prop in Ek as [_ HT]. apply Z.leb_le in HT. exact HT. }
      destruct (RcFrag.fg_close st g); cbn [negb fg_next];
        apply RcFragLib.rf_clear_length; apply RcFragLib.rf_fg_join_length; assumption.
    + cbn [fg_next]. apply RcFragLib.rf_clear_length. exact Hs.
Qed.

Lemma r13_rfg_len : forall inp b, length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RFG. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [snd];
    first [exact IH | apply r13_fgst_len; [exact IH | apply r13_rtg_len]].
Qed.

(* ---- spills and the side-arm frame record ---- *)

(* A spill at A + off (A the spill base in register 9) moves to a later state whose register 9 is the same and whose
   bytes at [A + off, A + off + 8) are the same. *)
Lemma r13_spill_keep : forall regs regs' m m' A off v,
  rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  getr regs' 9 = getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  spill regs m off v -> spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v Hr9 HA0 HA1 Hoff E9 HK (A' & HA' & Hq).
  assert (HA'eq : A' = A).
  { pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
    pose proof Hq as Hqb. destruct Hqb as (Hq0 & Hq1 & _).
    rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    rewrite (Z.mod_small A) in Hm by lia.
    assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
    rewrite HP in *. Z.div_mod_to_equations. lia. }
  subst A'. exists A. split; [unfold rg in *; rewrite E9; exact Hr9|].
  apply (r13_keep_bytes m m' _ _ Hq). rewrite length_le8. change (Z.of_nat 8) with 8.
  intros x Hx. exact (HK x Hx).
Qed.

(* FSREC moves to a state that keeps the 16 bytes at tp and every FakeStack byte outside the frame body. *)
Lemma r13_fsrec_keep : forall mem mem' fr,
  FSREC fr mem ->
  (forall i, 0 <= i < 16 -> mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i)) ->
  (forall x, AC.a_in_fs AC.ASYMS mem x -> ~ (fr + 24 <= x < fr + 3136) -> mbyte rsegs mem' x = mbyte rsegs mem x) ->
  FSREC fr mem'.
Proof.
  intros mem mem' fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) Htp' HK.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  assert (Hin : forall x, FS <= x < FS + AC.FS_SIZE -> AC.a_in_fs AC.ASYMS mem x)
    by (intros x Hx; exists FS; split; [exact HFSr | split; [exact Htp | exact Hx]]).
  exists FS, j.
  split.
  { intros k Hk. rewrite (Htp' (Z.of_nat k) ltac:(lia)). exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { apply (r13_keep_bytes mem mem' _ _ Hflag). cbn [length]. change (Z.of_nat 1) with 1.
    intros x Hx. apply HK; [apply Hin|]; lia. }
  { apply (r13_keep_bytes mem mem' _ _ Htail). rewrite length_le8. change (Z.of_nat 8) with 8.
    intros x Hx. rewrite HB6 in Hx. apply HK; [apply Hin|]; lia. }
Qed.

Section R13.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The inner lists of the allocator laws this file reads, taken apart once each, by statement where the law allows
   (a Theorem Labs lane 15:32Z: append-only at every level; a new generation touches these lemmas, not every site). *)
Lemma r13_matle : forall H mem md md', AsanLift.mat_le md md' ->
  (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md') /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md' = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md md' Hm.
  pose proof (AC.a_laws_mat_le _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md md' Hm) as P.
  decompose [and] P. split; [assumption | split; assumption].
Qed.

Lemma r13_blk : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_img a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md p n HAH Hin.
  destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md p n HAH Hin)
    as (_ & _ & X3 & _ & X5).
  split; [exact X3|]. intros a Ha. destruct (X5 a Ha) as (Y1 & _ & Y3 & _ & Y5). exact (conj Y1 (conj Y3 Y5)).
Qed.

Lemma r13_fsp : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md FS HAH Hw HFS.
  pose proof (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw HFS)
    as P.
  decompose [and] P. split; [assumption | split; assumption].
Qed.

Lemma r13_notown : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.in_blocks H a \/ AC.a_in_fs AC.ASYMS mem a \/
   AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a /\
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (shadow_addr a).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md a HAH Ha.
  apply (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md a HAH).
  destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha | right; right; left; exact Ha | right; right; right; exact Ha].
Qed.

Lemma r13_cli : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.in_blocks AC.a_client a ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md a HAH Ha.
  pose proof (AC.a_laws_client _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md a HAH) as P.
  decompose [and] P. auto.
Qed.

Lemma r13_cli_img : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.a_in_img a ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (shadow_addr a).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md a HAH Ha.
  pose proof (AC.a_laws_client _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md a HAH) as P.
  decompose [and] P. auto.
Qed.

(* ---- the segment lemma ---- *)

Lemma seg_R13 : forall b : nat, Hat B APIf ra (Inv_B81aa0_at B APIf ra) b -> Hat B APIf ra (Inv_B81860_at B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hb6 & HHB & Hr22 & HOUR & HCUR & HRBE &
    Hr21 & HIDB & HFGB & Hr20 & Ha0 & Hr27).
  subst c. rewrite SEGS.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HSbnd : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  pose proof (sl_frame_apart_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as HAPART.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HERRv : AC.a_errno AC.ASYMS = 6145452) by reflexivity.
  assert (HOOMv : AC.as_oom AC.ASYMS = 1227040) by reflexivity.
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  rewrite Haspz in HAPART.
  (* the run: 4 instructions to the allocator's free entry 0x534b4 *)
  apply (sl_run regs (Z_to_bv 64 0x81860) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x534b4 /\ mem' = mem /\
       getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = getr regs 20 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 27 = getr regs 27 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite r13_mkR_of.
    eapply evt_mono.
    + eapply r13_evt. unfold a0v, rg in Ha0. exact Ha0.
    + intros ms' (R & Hms & P1 & P10 & P2 & P3 & P4 & P8 & P9 & P27 & P19 & P21 & P22 & P23 & P25 & P26).
      exists R, (Z_to_bv 64 0x534b4), mem. split; [exact Hms|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact P1|]. split; [exact P10|].
      split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P27|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|].
      split; [exact P23|].
      split; [exact P25 | exact P26].
  - intros R pc' mem' regs'' md'
      (Hpc & Hmem & K1 & K10 & K2 & K3 & K4 & K8 & K9 & K27 & K19 & K21 & K22 & K23 & K25 & K26) Hreg Hmat.
    subst pc' mem'.
    assert (E1 : getr regs'' 1 = Z_to_bv 64 0x81aa0) by (rewrite Hreg; exact K1).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 phi) by (rewrite Hreg, K10; exact Hr20).
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (HFRAc : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs regs'' mem md md' HFRA);
          [exact E2 | exact E3 | exact E4 | exact E8 | exact E9 | exact E19 | exact E26 | exact Hmat]).
    assert (HENTc : ENT APIf g (hb1 phi (rnb g b)) mem md') by (eapply ent_mat; [exact HENT | exact Hmat]).
    destruct (r13_matle (hb1 phi (rnb g b) ++ g_H g) mem md md' Hmat) as (HAHm & Hlom & Hhim).
    assert (HAH' : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md')
      by exact (HAHm HAH).
    assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md')
      by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS _ mem md' HAH').
    assert (Hstklo' : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= g_S g - AF.SLOT_STACK)
      by (rewrite Hlom; exact Hstklo).
    rewrite HHMv in Hhigh.
    (* the free pre at the call, from FRA + ENT *)
    assert (HPREc : AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
                      AC.AK_FREE (hb1 phi (rnb g b) ++ g_H g) regs'' mem md').
    { apply (fra_call_pre B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem md' AC.AK_FREE HFRAc HENTc).
      - unfold YK0s.ret_ok. rewrite E1. vm_compute. reflexivity.
      - unfold AC.AK_FREE. rewrite HFN. lia. }
    (* the allocator's free, on the frame's law: the live list is [] ++ (Phi, n) :: g_H g *)
    pose proof (AC.aa_free AC.ASYMS AsanRTInv.RT (APIf rc)) as HFREE.
    unfold AC.afree_contract, AC.afree_at in HFREE.
    assert (EF : AC.as_free AC.ASYMS = 0x534b4) by reflexivity.
    eapply (SR_bind rsegs).
    + (* the free's per-class premises, from ENT's 14th conjunct (Tac_cls.sl_free_cls, Bc := Bc_of BE) *)
      destruct (sl_free_cls APIf g (hb1 phi (rnb g b)) mem md' phi (rnb g b) HENTc) as (BE & _ & _ & HB1 & HB2).
      rewrite <- EF. exact (HFREE [] (g_H g) regs'' mem md' phi (rnb g b) (Bc_of BE) HPREc E10 HB1 HB2).
    + intros c' (regs3 & mem3 & md3 & Ec' & HPOST & HKERR).
      rewrite E1 in Ec'. subst c'.
      change ([] ++ (phi, rnb g b) :: g_H g) with (hb1 phi (rnb g b) ++ g_H g) in HPOST.
      (* the post's projections *)
      pose proof HPOST as HAH3; apply AC.a_call_post_ah in HAH3.
      pose proof HPOST as HKR; apply AC.a_call_post_regs in HKR.
      pose proof HPOST as HMOD; apply AC.a_call_post_model in HMOD.
      pose proof HPOST as HSTK3; apply AC.a_call_post_stklo in HSTK3.
      assert (HTP3 : forall i, 0 <= i < 16 ->
                mbyte rsegs mem3 (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
        by (eapply AC.a_call_post_tp; exact HPOST).
      assert (HWIN3 : forall a, AC.a_window AC.AK_FREE regs'' a -> writable_at rsegs mem3 a)
        by (eapply AC.a_call_post_win_writable; exact HPOST).
      assert (HWP : forall a, AC.a_window AC.AK_FREE regs'' a -> exists bb, mbyte rsegs mem3 a = Some bb)
        by (eapply AC.a_call_post_win_present; exact HPOST).
      assert (HFRM : forall a, 0 <= a < 2 ^ 64 ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md' a ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 a ->
                ~ AC.a_window AC.AK_FREE regs'' a ->
                ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) -> a <> AC.as_oom AC.ASYMS ->
                ~ (phi <= a < phi + rnb g b) ->
                mbyte rsegs mem3 a = mbyte rsegs mem a /\
                (writable_at rsegs mem a <-> writable_at rsegs mem3 a))
        by (eapply AC.a_call_post_frame; exact HPOST).
      (* the freed block: app memory below stklo, off the image and off the side stack *)
      assert (Hpin : In (phi, rnb g b) (hb1 phi (rnb g b) ++ g_H g)) by (left; reflexivity).
      destruct (r13_blk _ mem md' phi (rnb g b) HAH' Hpin) as (Hplo & Hpall).
      (* callee-saved registers *)
      assert (G2 : getr regs3 2 = getr regs'' 2)
        by (apply (r13_regs_kept_at regs'' regs3 2 2 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G3 : getr regs3 3 = getr regs'' 3)
        by (apply (r13_regs_kept_at regs'' regs3 3 3 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G4 : getr regs3 4 = getr regs'' 4)
        by (apply (r13_regs_kept_at regs'' regs3 4 4 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G8 : getr regs3 8 = getr regs'' 8)
        by (apply (r13_regs_kept_at regs'' regs3 8 8 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G9 : getr regs3 9 = getr regs'' 9)
        by (apply (r13_regs_kept_at regs'' regs3 9 9 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G27 : getr regs3 27 = getr regs'' 27)
        by (apply (r13_regs_kept_at regs'' regs3 27 27 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G19 : getr regs3 19 = getr regs'' 19)
        by (apply (r13_regs_kept_at regs'' regs3 19 19 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G21 : getr regs3 21 = getr regs'' 21)
        by (apply (r13_regs_kept_at regs'' regs3 21 21 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G22 : getr regs3 22 = getr regs'' 22)
        by (apply (r13_regs_kept_at regs'' regs3 22 22 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G23 : getr regs3 23 = getr regs'' 23)
        by (apply (r13_regs_kept_at regs'' regs3 23 23 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G25 : getr regs3 25 = getr regs'' 25)
        by (apply (r13_regs_kept_at regs'' regs3 25 25 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G26 : getr regs3 26 = getr regs'' 26)
        by (apply (r13_regs_kept_at regs'' regs3 26 26 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      (* the window of the allocator entry, in the caller's terms *)
      assert (Haspc : AC.aspZ regs'' = sp) by (unfold AC.aspZ; rewrite E2; exact Haspz).
      assert (HWv : forall x, AC.a_window AC.AK_FREE regs'' x <-> sp - 4096 <= x < sp)
        by (intros x; unfold AC.a_window, AC.AK_FREE; rewrite Haspc; tauto).
      (* ownership classes: the real stack, the side stack, their shadow bytes, the client cells, the shadow bytes
         of image bytes and the read-only image bytes are never the allocator's, in either state *)
      assert (NO1 : forall x, AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                      AC.a_in_fs AC.ASYMS mem x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md' x /\
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md'
                          (shadow_addr x)).
      { intros x Hx. apply (r13_notown _ mem md' x HAH').
        destruct Hx as [Hx|Hx]; [right; right; exact Hx | right; left; exact Hx]. }
      assert (Hfsmem : forall x, AC.a_in_fs AC.ASYMS mem x -> AC.a_in_fs AC.ASYMS mem3 x).
      { intros x (FSb & HFSr & Hw & Hr). exists FSb. split; [exact HFSr|]. split; [|exact Hr].
        intros k Hk. rewrite (HTP3 (Z.of_nat k) ltac:(lia)). exact (Hw k Hk). }
      assert (NO2 : forall x, AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                      AC.a_in_fs AC.ASYMS mem x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 x /\
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 (shadow_addr x)).
      { intros x Hx.
        apply (r13_notown ([] ++ g_H g) mem3 md3 x HAH3).
        destruct Hx as [Hx|Hx]; [right; right; rewrite HSTK3; exact Hx
                                | right; left; exact (Hfsmem x Hx)]. }
      assert (NOc1 : forall x, AC.in_blocks AC.a_client x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md' x)
        by (intros x Hx; exact (r13_cli _ mem md' x HAH' Hx)).
      assert (NOc2 : forall x, AC.in_blocks AC.a_client x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 x)
        by (intros x Hx; exact (r13_cli ([] ++ g_H g) mem3 md3 x HAH3 Hx)).
      assert (NOi1 : forall x, AC.a_in_img x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md'
                          (shadow_addr x))
        by (intros x Hx; exact (r13_cli_img _ mem md' x HAH' Hx)).
      assert (NOi2 : forall x, AC.a_in_img x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 (shadow_addr x))
        by (intros x Hx; exact (r13_cli_img ([] ++ g_H g) mem3 md3 x HAH3 Hx)).
      (* THE TRANSPORT: a byte the allocator entry may not touch keeps its value and its writability *)
      assert (KEEP : forall x, 0 <= x < 2 ^ 64 ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md' x ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem3 md3 x ->
                ~ (sp - 4096 <= x < sp) ->
                ~ (AC.a_errno AC.ASYMS <= x < AC.a_errno AC.ASYMS + 4) -> x <> AC.as_oom AC.ASYMS ->
                ~ (phi <= x < phi + rnb g b) ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx No1 No2 Nw Ne Noo Nt.
        apply (HFRM x Hx No1 No2); [ intro Hc; apply Nw; exact (proj1 (HWv x) Hc)
                                   | exact Ne | exact Noo | exact Nt]. }
      (* class A: the real stack at or above sp *)
      assert (KST : forall x, sp <= x <= g_S g ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx. apply KEEP; try lia.
        - apply NO1. left. lia.
        - apply NO2. left. lia. }
      (* class F: the side stack's bytes *)
      assert (KFS : forall x, AC.a_in_fs AC.ASYMS mem x ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx. pose proof Hx as Hx'. destruct Hx' as (FSb & HFSr & Hw & Hr).
        destruct (r13_fsp _ mem md' FSb HAH' Hw HFSr) as (HGT & Hend & Happ).
        pose proof (Happ x Hr) as Happx.
        unfold app_mem in Happx.
        apply KEEP.
        - lia.
        - exact (proj1 (NO1 x (or_intror Hx))).
        - exact (proj1 (NO2 x (or_intror Hx))).
        - lia.
        - lia.
        - lia.
        - intro Hc. exact (proj2 (proj2 (Hpall x Hc)) Hx). }
      (* the frame bytes are on the real stack or in the side stack *)
      assert (HFRC : forall x, fr <= x < fr + 3136 ->
                AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                AC.a_in_fs AC.ASYMS mem x).
      { intros x Hx. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
        - left. rewrite Hlom. exact (Hreal x Hx).
        - right. exact (Hfs x Hx). }
      (* class B: the frame, on either arm *)
      assert (KFR : forall x, fr <= x < fr + 3136 ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx. destruct (HFRC x Hx) as [Hc|Hc]; [|exact (KFS x Hc)].
        apply KEEP.
        - lia.
        - exact (proj1 (NO1 x (or_introl Hc))).
        - exact (proj1 (NO2 x (or_introl Hc))).
        - intro Hc2. exact (HAPART x Hx Hc2).
        - lia.
        - lia.
        - lia. }
      (* class C: the shadow bytes of real-stack and side-stack bytes *)
      assert (KSHX : forall x, AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                       AC.a_in_fs AC.ASYMS mem x ->
                mbyte rsegs mem3 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
      { intros x Hcls.
        assert (Happx : app_mem x).
        { destruct Hcls as [Hc|Hc].
          - unfold app_mem. lia.
          - destruct Hc as (FSb & HFSr & Hw & Hr).
            destruct (r13_fsp _ mem md' FSb HAH' Hw HFSr) as (_ & _ & Happ). exact (Happ x Hr). }
        assert (Hshd : in_shadow (shadow_addr x)) by (apply shadow_of_app; exact Happx).
        pose proof (in_shadow_range _ Hshd) as Hrr.
        pose proof Hshd as Hshd'.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshd'.
        refine (proj1 (KEEP (shadow_addr x) _ _ _ _ _ _ _)).
        - lia.
        - exact (proj2 (NO1 _ Hcls)).
        - exact (proj2 (NO2 _ Hcls)).
        - lia.
        - lia.
        - lia.
        - intro Hc. destruct (Hpall _ Hc) as (Happq & _).
          exact (app_not_shadow _ Happq Hshd). }
      assert (KSH : forall x, 0 <= x < 392 ->
                mbyte rsegs mem3 (Sfr fr + x) = mbyte rsegs mem (Sfr fr + x)).
      { intros x Hx. rewrite <- r13_sh8. apply KSHX. apply HFRC. lia. }
      (* class D: the shadow bytes of image bytes *)
      assert (KAG : forall x, AC.a_in_img x ->
                mbyte rsegs mem3 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
      { intros x Hx.
        pose proof (r13_img_range x Hx) as Himgb.
        assert (Hshd : in_shadow (shadow_addr x)) by (apply shadow_of_app; unfold app_mem; lia).
        pose proof (in_shadow_range _ Hshd) as Hrr.
        pose proof Hshd as Hshd'.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshd'.
        refine (proj1 (KEEP (shadow_addr x) _ _ _ _ _ _ _)).
        - lia.
        - exact (NOi1 x Hx).
        - exact (NOi2 x Hx).
        - lia.
        - lia.
        - lia.
        - intro Hc. destruct (Hpall _ Hc) as (Happx & _).
          exact (app_not_shadow _ Happx Hshd). }
      (* class E: the musl client cells the sink words live in *)
      assert (KCL : forall x, AC.in_blocks AC.a_client x -> AC.a_in_img x ->
                ~ (AC.a_errno AC.ASYMS <= x < AC.a_errno AC.ASYMS + 4) -> x <> AC.as_oom AC.ASYMS ->
                mbyte rsegs mem3 x = mbyte rsegs mem x).
      { intros x Hcl Himg Ne Noo.
        pose proof (r13_img_range x Himg) as Hr.
        refine (proj1 (KEEP x _ _ _ _ _ _ _)).
        - lia.
        - exact (NOc1 x Hcl).
        - exact (NOc2 x Hcl).
        - lia.
        - exact Ne.
        - exact Noo.
        - intro Hc. exact (proj1 (proj2 (Hpall x Hc)) Himg). }
      (* class G: the image's read-only bytes (the box bytes at BOXA, the catalogue's row-name strings) *)
      assert (KRO : forall x, 0x21140 <= x < 0x218f0 -> mbyte rsegs mem3 x = mbyte rsegs mem x).
      { intros x Hx. pose proof (r13_ro_in x Hx) as Hro'. pose proof (r13_ro_img x Hro') as Himg.
        refine (proj1 (KEEP x _ _ _ _ _ _ _)).
        - lia.
        - exact (AC.a_laws_ro_not_owned _ _ _ _ _ ALAWS _ mem md' x HAH' Hro').
        - exact (AC.a_laws_ro_not_owned _ _ _ _ _ ALAWS _ mem3 md3 x HAH3 Hro').
        - lia.
        - lia.
        - lia.
        - intro Hc. exact (proj1 (proj2 (Hpall x Hc)) Himg). }
      (* the image's RELRO bytes (the row table at BA_FR + 72, the catalogue row at mrow): frame_facts says the
         runtime owns none of them, in any state *)
      pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRimg & HOWNG & _).
      assert (KRELRO : forall x, 0x9f168 <= x < 0x9f168 + 9344 -> mbyte rsegs mem3 x = mbyte rsegs mem x).
      { intros x Hx. pose proof (r13_relro_in x Hx) as Hin.
        refine (proj1 (KEEP x _ _ _ _ _ _ _)).
        - lia.
        - exact (fun X => proj2 (HOWNG rc _ _ _ _ X) Hin).
        - exact (fun X => proj2 (HOWNG rc _ _ _ _ X) Hin).
        - lia.
        - lia.
        - lia.
        - intro Hc. exact (proj1 (proj2 (Hpall x Hc)) (HRimg x Hin)). }
      assert (Hgimg3 : G_img_c B AF.frame_RELRO mem3).
      { intros a Ha. pose proof (Hgimg a Ha) as Hg0. pose proof (r13_relro_range a Ha) as Hra.
        rewrite SEGS in Hg0 |- *.
        destruct (KEEP a ltac:(lia)
                    (fun X => proj2 (HOWNG rc _ _ _ _ X) Ha) (fun X => proj2 (HOWNG rc _ _ _ _ X) Ha)
                    ltac:(lia) ltac:(lia) ltac:(lia)
                    (fun Hc => proj1 (proj2 (Hpall a Hc)) (HRimg a Ha))) as (Hmb & _).
        rewrite Hmb. exact Hg0. }
      (* the input block (for g_n > 0 a live block of g_H g, apart from the freed block): its bytes and their
         shadow bytes are the allocator's in neither state *)
      assert (KINP : forall x, g_p g <= x < g_p g + g_n g ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                mbyte rsegs mem3 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
      { intros x Hx.
        assert (Hn0 : 0 < g_n g) by lia.
        destruct (Hinblk Hn0) as (Hin & _).
        destruct (fra_in_apart B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA x Hx)
          as (Happ & Hlo2 & Hnfr & Himg).
        assert (Hr64 : 0 <= x < 2 ^ 64)
          by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happ; lia).
        assert (Hinb1 : AC.in_blocks (hb1 phi (rnb g b) ++ g_H g) x)
          by (exists (g_p g), (g_n g); split; [apply in_or_app; right; exact Hin | lia]).
        assert (Hinb2 : AC.in_blocks ([] ++ g_H g) x) by (exists (g_p g), (g_n g); split; [exact Hin | lia]).
        assert (Hnt : ~ (phi <= x < phi + rnb g b)).
        { destruct (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md' phi (rnb g b) (g_p g) (g_n g) HAH' Hin)
            as [D|D]; lia. }
        pose proof (r13_notown _ mem md' x HAH' (or_introl Hinb1)) as (No1 & Ns1).
        pose proof (r13_notown _ mem3 md3 x HAH3 (or_introl Hinb2)) as (No2 & Ns2).
        split.
        - refine (proj1 (KEEP x Hr64 No1 No2 _ _ _ Hnt)).
          + lia.
          + intro He. exact (Himg (errno_in_img x He)).
          + intro He. apply Himg. rewrite He. exact oom_in_img.
        - assert (Hshd : in_shadow (shadow_addr x)) by (apply shadow_of_app; exact Happ).
          pose proof (in_shadow_range _ Hshd) as Hrr.
          pose proof Hshd as Hshd'.
          unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshd'.
          refine (proj1 (KEEP (shadow_addr x) _ Ns1 Ns2 _ _ _ _)).
          + lia.
          + lia.
          + lia.
          + lia.
          + intro Hc. destruct (Hpall _ Hc) as (Happq & _). exact (app_not_shadow _ Happq Hshd). }
      assert (HINPb : bytes_at rsegs mem3 (g_p g) (g_in g)).
      { apply (r13_keep_bytes mem mem3 _ _ Hinb). intros x Hx. exact (proj1 (KINP x Hx)). }
      assert (HINPad : 0 < g_n g -> addressable mem3 (g_p g) (g_n g)).
      { intro Hn0. destruct (Hinblk Hn0) as (_ & Had).
        apply (r13_addr_keep mem mem3 (g_p g) (g_n g) Had).
        intros i Hi. exact (proj2 (KINP (g_p g + i) ltac:(lia))). }
      assert (Hsn3 : sink_none B mem3 md3).
      { pose proof FF as (_ & _ & _ & _ & Hhead & Hlock & Hthr & _).
        pose proof HFRAc as (A2 & sp2 & s52 & _ & _ & _ & Hsnc & _).
        destruct Hsnc as ((Hthrm & Hlockm) & Hohd & Hfd).
        destruct HMOD as (lz & mt & vm' & Emd3).
        split; [split|split].
        - eapply YI14.val_mem_frame; [|exact Hthrm].
          intros x Hx. rewrite Hthr in Hx. cbn in Hx. try rewrite SEGS.
          apply KCL.
          + apply r13_client_a. lia.
          + exact (r13_img_cov_in 0x5fc8e1 0x5fc8e2 x r13_sink_cov_a ltac:(lia)).
          + lia.
          + lia.
        - eapply YI14.val_mem_frame; [|exact Hlockm].
          intros x Hx. rewrite Hlock in Hx. cbn in Hx. try rewrite SEGS.
          apply KCL.
          + apply r13_client_b. lia.
          + exact (r13_img_cov_in 0x5fcd40 0x5fcd50 x r13_sink_cov_b ltac:(lia)).
          + lia.
          + lia.
        - intros k Hk. pose proof (Hohd k Hk) as Hk'.
          try rewrite SEGS in Hk'. try rewrite SEGS.
          rewrite KCL.
          + exact Hk'.
          + apply r13_client_b. rewrite Hhead. lia.
          + eapply r13_img_cov_in; [exact r13_sink_cov_b | rewrite Hhead; lia].
          + rewrite Hhead. lia.
          + rewrite Hhead. lia.
        - rewrite Emd3. exact Hfd. }
      assert (Hwin3 : stk rsegs mem3 (g_S g - AF.SLOT_STACK) (g_S g)).
      { pose proof Hwin as HwinD. destruct HwinD as (W0 & W1 & W).
        split; [exact W0|]. split; [exact W1|].
        intros x Hx.
        destruct (Z_lt_le_dec x sp) as [Hbelow|Habove].
        - destruct (Z_lt_le_dec x (sp - 4096)) as [Hlow|Hupw].
          + assert (Hcls : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END) by lia.
            destruct (W x Hx) as (Hw & bb & Hb).
            destruct (KEEP x ltac:(lia) (proj1 (NO1 x (or_introl Hcls)))
                        (proj1 (NO2 x (or_introl Hcls))) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(lia)) as (Hmb & Hwr).
            split; [exact (proj1 Hwr Hw)|]. exists bb. rewrite <- Hb. exact Hmb.
          + assert (Hwx : AC.a_window AC.AK_FREE regs'' x) by (apply (HWv x); lia).
            split; [exact (HWIN3 x Hwx) | exact (HWP x Hwx)].
        - destruct (W x Hx) as (Hw & bb & Hb).
          destruct (KST x ltac:(lia)) as (Hmb & Hwr).
          split; [exact (proj1 Hwr Hw)|]. exists bb. rewrite <- Hb. exact Hmb. }
      assert (HAG3 : forall a, in_globals AF.frame_AG a -> addressable mem3 a 1).
      { intros a Hin. apply (r13_addr_keep mem mem3 a 1 (HAG a Hin)).
        intros i Hi. replace (a + i) with a by lia. apply KAG. exact (r13_ag_img a Hin). }
      (* the slot window outside the frame stays addressable: its shadow bytes are real-stack shadow *)
      assert (HWA3 : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) ->
                addressable mem3 a 1).
      { intros a H1 H2. apply (r13_addr_keep mem mem3 a 1 (HWA a H1 H2)).
        intros i Hi. replace (a + i) with a by lia. apply KSHX. left. lia. }
      (* the frame record of the side arm *)
      assert (HREC3 : FSREC fr mem -> FSREC fr mem3).
      { intros HR. apply (r13_fsrec_keep mem mem3 fr HR HTP3).
        intros x Hx _. exact (proj1 (KFS x Hx)). }
      (* the spills and the frame words at mem3 *)
      assert (Q336 : q64 mem3 (A + 336) fr).
      { apply (r13_keep_bytes mem mem3 _ _ Hspill). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KST x ltac:(lia))). }
      assert (Q40 : q64 mem3 (A + 40) fr).
      { apply (r13_keep_bytes mem mem3 _ _ Hfr56). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KST x ltac:(lia))). }
      assert (Qsaved : bytes_at rsegs mem3 (g_S g - 104) (saved_bytes ra g)).
      { apply (r13_keep_bytes mem mem3 _ _ Hsaved).
        unfold saved_bytes. rewrite !length_app, !length_le8. cbn [Nat.add].
        change (Z.of_nat 104) with 104. intros x Hx. exact (proj1 (KST x ltac:(lia))). }
      assert (Qhdr1 : q64 mem3 fr 0x41b58ab3).
      { apply (r13_keep_bytes mem mem3 _ _ Hhdr1). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (Qhdr2 : q64 mem3 (fr + 16) AF.ENTRY).
      { apply (r13_keep_bytes mem mem3 _ _ Hhdr2). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (QOUR : OURb g fr mem3).
      { unfold OURb in *. apply (r13_keep_bytes mem mem3 _ _ HOUR). rewrite OUR_length.
        change (Z.of_nat 6) with 6. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (Qsh : exists sh, bytes_at rsegs mem3 (Sfr fr) sh /\ length sh = 392%nat).
      { destruct Hsh as (sh & Hb & Hl). exists sh. split; [|exact Hl].
        apply (r13_keep_bytes mem mem3 _ _ Hb). rewrite Hl, HFSv.
        change (Z.of_nat (Z.to_nat 392)) with 392. intros x Hx.
        replace x with (Sfr fr + (x - Sfr fr)) by lia. apply KSH. lia. }
      (* the turn-(S b) records, in the frame *)
      assert (QIDB : IDBr g fr (RID (g_in g) (S b)) mem3).
      { unfold IDBr in *. apply (r13_keep_bytes mem mem3 _ _ HIDB). rewrite r13_rid_len.
        change (Z.of_nat 38) with 38. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (QFGB : FGBr g fr (RFG (g_in g) (S b)) mem3).
      { unfold FGBr in *. apply (r13_keep_bytes mem mem3 _ _ HFGB). rewrite r13_rfg_len.
        change (Z.of_nat 72) with 72. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (QCUR : CUR g 7 regs3).
      { destruct HCUR as (Hc0 & Hc23 & Hc25). split; [exact Hc0|].
        unfold rg in Hc23, Hc25 |- *.
        split; [rewrite G23, E23; exact Hc23 | rewrite G25, E25; exact Hc25]. }
      (* FRA at the exit: the live list is g_H g, hb = [] *)
      assert (HFRAx : FRA B APIf ra g fr [] regs3 mem3 md3).
      { apply (sl_mid B APIf ra g fr (hb1 phi (rnb g b)) [] regs'' mem md' regs3 mem3 md3
                 (fun a => phi <= a < phi + rnb g b) AC.AK_FREE HFRAc HPOST).
        - cbn [length]. lia.
        - exact Hsn3.
        - exact Hgimg3.
        - exact Qhdr1.
        - exact Qhdr2.
        - intros A2 HA2 HA2r. rewrite E9 in HA2.
          assert (EA2 : A2 = A) by exact (r13_rg_eq regs 9 A2 A HA2 Hr9 HA2r HA64). subst A2. exact Q336.
        - intros A2 HA2 HA2r v Hv. rewrite E9 in HA2.
          assert (EA2 : A2 = A) by exact (r13_rg_eq regs 9 A2 A HA2 Hr9 HA2r HA64). subst A2.
          apply (r13_keep_bytes mem mem3 _ _ Hv). rewrite length_le8.
          change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KST x ltac:(lia))).
        - intros A2 HA2 HA2r. rewrite E9 in HA2.
          assert (EA2 : A2 = A) by exact (r13_rg_eq regs 9 A2 A HA2 Hr9 HA2r HA64). subst A2. exact Q40.
        - exact Qsh.
        - exact Qsaved.
        - exact Hwin3.
        - exact HAG3.
        - exact HWA3.
        - exact HREC3.
        - exact HINPb.
        - exact HINPad.
        - rewrite G2; reflexivity.
        - rewrite G3; reflexivity.
        - rewrite G4; reflexivity.
        - rewrite G8; reflexivity.
        - rewrite G9; reflexivity.
        - rewrite G19; reflexivity.
        - rewrite G26; reflexivity. }
      (* ENT at the exit: the touched bytes are the freed block *)
      assert (HENTx : ENT APIf g [] mem3 md3).
      { apply (ent_call B APIf ra g fr (hb1 phi (rnb g b)) [] regs'' mem md' regs3 mem3 md3
                 (fun a => phi <= a < phi + rnb g b) AC.AK_FREE HENTc HFRAc HPOST).
        - unfold AC.AK_FREE. rewrite HFN. lia.
        - intros a Ha. cbv beta in Ha. destruct (Hpall a Ha) as (Happ & Himg & _).
          split; [exact Happ|]. split; [lia|]. split; [exact Himg|].
          intros (q & k & Hin & Hr).
          destruct (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md' phi (rnb g b) q k HAH' Hin)
            as [D|D]; lia.
        - exact HKERR. }
      (* RBE at the exit: the 33 spills (above the spill base A >= sp), OUTA, the identity record's 38 bytes,
         our[] and the fragment record's 72 bytes (frame bytes, kept through their shadow), the row-name clause
         (read-only image) and the row table / box / catalogue-row bytes (RELRO / read-only image) *)
      assert (HRBE3 : RBE g fr regs3 mem3).
      { destruct HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
                          S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUTA & Hid38 & HNM & Hour6 &
                          Htbl & Hbox & Hmrow &
                          (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b) & S152 & S112 &
                          HA2256 & S160).
        assert (E9' : getr regs3 9 = getr regs 9) by (rewrite G9; exact E9).
        assert (HA0 : 0 <= A) by lia.
        assert (HA1 : A + 448 <= 2 ^ 64) by lia.
        assert (HKA : forall off, 0 <= off <= 440 -> forall x, A + off <= x < A + off + 8 ->
                  mbyte rsegs mem3 x = mbyte rsegs mem x)
          by (intros off Hoff x Hx; exact (proj1 (KST x ltac:(lia)))).
        assert (KS : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs3 mem3 off v)
          by (intros off v Hoff Hs; exact (r13_spill_keep regs regs3 mem mem3 A off v Hr9 HA0 HA1 Hoff E9'
                                             (HKA off Hoff) Hs)).
        unfold RBE.
        split; [exact (KS 128 _ ltac:(lia) S128)|].
        split; [exact (KS 312 _ ltac:(lia) S312)|].
        split; [exact (KS 272 _ ltac:(lia) S272)|].
        split; [exact (KS 264 _ ltac:(lia) S264)|].
        split; [exact (KS 256 _ ltac:(lia) S256)|].
        split; [exact (KS 248 _ ltac:(lia) S248)|].
        split; [exact (KS 56 _ ltac:(lia) S56)|].
        split; [exact (KS 184 _ ltac:(lia) S184)|].
        split; [exact (KS 144 _ ltac:(lia) S144)|].
        split; [exact (KS 8 _ ltac:(lia) S8)|].
        split; [exact (KS 32 _ ltac:(lia) S32)|].
        split; [exact (KS 24 _ ltac:(lia) S24)|].
        split; [exact (KS 16 _ ltac:(lia) S16)|].
        split; [exact (KS 96 _ ltac:(lia) S96)|].
        split; [exact (KS 120 _ ltac:(lia) S120)|].
        split; [exact (KS 240 _ ltac:(lia) S240)|].
        split; [exact (KS 232 _ ltac:(lia) S232)|].
        split; [exact (KS 224 _ ltac:(lia) S224)|].
        split; [exact (KS 176 _ ltac:(lia) S176)|].
        split; [exact (KS 208 _ ltac:(lia) S208)|].
        split; [exact (KS 64 _ ltac:(lia) S64)|].
        split.
        { unfold OUTA in *. apply (r13_addr_keep mem mem3 (fr + 544) 1492 HOUTA).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        split.
        { apply (r13_addr_keep mem mem3 (fr + 2176) 38 Hid38).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        split.
        { intros Hnm. destruct (HNM Hnm) as (Hok & Hbs & Had & Hpos & Hhi).
          destruct Hnm as (Hh & Hrn).
          pose proof (r13_rname (g_in g) Hh Hrn) as Hrng.
          pose proof (r13_nb_len (g_in g)) as Hlen.
          split; [exact Hok|]. split.
          - apply (r13_keep_bytes mem mem3 _ _ Hbs). intros x Hx. apply KRO. lia.
          - split; [|split; [exact Hpos | exact Hhi]].
            apply (r13_addr_keep mem mem3 _ _ Had). intros i Hi. apply KAG. apply r13_ro_img. apply r13_ro_in.
            lia. }
        split.
        { apply (r13_addr_keep mem mem3 (fr + 2624) 6 Hour6).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        split.
        { apply (r13_keep_bytes mem mem3 _ _ Htbl). rewrite r13_tbl_len.
          assert (EBA : BAC.BA_FR = 656896) by reflexivity.
          intros x Hx. apply KRELRO. rewrite EBA in Hx. lia. }
        split.
        { apply (r13_keep_bytes mem mem3 _ _ Hbox).
          assert (Hl6 : Z.of_nat (length box6) = 6) by reflexivity.
          assert (EBOX : BOXA = 135488) by reflexivity.
          rewrite Hl6. intros x Hx. apply KRO. rewrite EBOX in Hx. lia. }
        split.
        { apply (r13_keep_bytes mem mem3 _ _ Hmrow). rewrite r13_mb_len.
          pose proof (r13_mrow_range (g_in g)) as Hmr.
          intros x Hx. apply KRELRO. lia. }
        split.
        { unfold PRA.
          split; [exact (KS 136 _ ltac:(lia) P136)|]. split; [exact (KS 280 _ ltac:(lia) P280)|].
          split; [exact (KS 168 _ ltac:(lia) P168)|]. split; [exact (KS 192 _ ltac:(lia) P192)|].
          split; [exact (KS 200 _ ltac:(lia) P200)|]. split; [exact (KS 216 _ ltac:(lia) P216)|].
          split; [exact (KS 104 _ ltac:(lia) P104)|]. split; [exact (KS 288 _ ltac:(lia) P288)|].
          split; [exact (KS 296 _ ltac:(lia) P296)|]. split; [exact (KS 304 _ ltac:(lia) P304)|].
          exact (KS 168 _ ltac:(lia) P168b). }
        split; [exact (KS 152 _ ltac:(lia) S152)|].
        split; [exact (KS 112 _ ltac:(lia) S112)|].
        split.
        { apply (r13_addr_keep mem mem3 (fr + 2256) 72 HA2256).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        exact (KS 160 _ ltac:(lia) S160). }
      (* the exit cut *)
      rewrite <- SEGS. apply Hexit.
      exists regs3, mem3, md3, fr.
      split; [reflexivity|].
      split; [exact HFRAx|].
      split; [exact HENTx|].
      split; [exact Hgn|].
      split; [exact Hb6|].
      split; [unfold rg in Hr22 |- *; rewrite G22, E22; exact Hr22|].
      split; [exact QOUR|].
      split; [exact HRBE3|].
      split; [unfold rg in Hr21 |- *; rewrite G21, E21; exact Hr21|].
      split.
      { split; [exact Hb6|].
        split; [exact QCUR|].
        split; [exact QOUR|].
        split; [unfold rg in Hr22 |- *; rewrite G22, E22; exact Hr22|].
        split; [exact QIDB | exact QFGB]. }
      unfold rg in Hr27 |- *. rewrite G27, E27. exact Hr27.
Qed.

End R13.
