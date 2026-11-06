(** cross_check (reac_segconf.c:303-325, static) in the UBSan image 1696d6c34ffd (U/Prog/cross_check_c.v, 0x15ec4,
    75 instructions, frame 0x50: ra and s0-s8). The same walk as Prog/cross_check.v over this build's image and
    contracts; the image-free lemmas (CCSpine: byte lists, the spine, the encodings, and the memory lemmas over any
    segment list) are imported from there. refuse (0x15c80) is a premise.

    What UBSan adds over the plain build: four checks, all dead under the
    premise, each branching to the single `unimp` at 0x15fec:
      0x15ef0  c = 0        (null)          -- cross_check_pre: c <> 0
      0x15efc  c & 7 <> 0   (alignment)     -- cross_check_pre: c mod 16 = 0
      0x15f38  i = 33       (array bounds)  -- i < n <= 32 (rconf_enc)
      0x15f3c  ~c < 356 i   (pointer wrap)  -- c + 16616 <= 2^64 (bytes_at)
    Its frame is 0x50 (ra, s0-s8); s5 carries 356 i and s6 the index i, s7 = ~c and s8 = 33. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env refuse_c cross_check_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require cross_check.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.cross_check.CCSpine.
Import ListNotations.
Open Scope Z_scope.

(** The comparisons of the UBSan checks, and the alignment one of them leaves. *)
Lemma cc_eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma cc_ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma cc_land7 : forall z, 0 <= z < 2^64 -> z mod 16 = 0 -> Z.land z 7 = 0.
Proof.
  intros z H0 H16. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. Z.div_mod_to_equations. lia.
Qed.


(** ** The image and the machine, for the walk *)
(** A mapped address lies in the image's span. *)
Lemma cc_fs_in_range : forall (sl : list Segment) z lo hi,
  forallb (fun s => (lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi)) sl = true ->
  find_segment sl z 1 <> None -> lo <= z < hi.
Proof.
  induction sl as [|sg rest IH]; intros z lo hi Hall H; cbn [find_segment] in H; [exfalso; apply H; reflexivity|].
  cbn [forallb] in Hall. apply andb_prop in Hall as [H1 H2]. apply andb_prop in H1 as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2.
  destruct (Z.leb_spec (Z.of_N (seg_base sg)) z); cbn [andb] in H;
    [destruct (Z.leb_spec (z + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))); [lia|]|];
    eapply IH; eauto.
Qed.

Lemma cc_fs_range : forall z, find_segment rsegs z 1 <> None -> 65536 <= z < 348160.
Proof. intros z H. apply (cc_fs_in_range rsegs z 65536 348160); [vm_compute; reflexivity | exact H]. Qed.

(** Every address of the image's span lies in one of its reserved (page-rounded) segments: the four PT_LOADs are
    page-aligned and abut, [0x10000, 0x54000). *)
Lemma cc_resv_nth : forall k, (k < 4)%nat ->
  In (nth k (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)) (segments_reserved rsegs).
Proof.
  intros k Hk. apply nth_In.
  assert (L : length (segments_reserved rsegs) = 4%nat) by (vm_compute; reflexivity). lia.
Qed.

Lemma cc_resv_cover : forall z, 65536 <= z < 348160 ->
  exists s, In s (segments_reserved rsegs) /\ bv_unsigned (fst s) <= z < bv_unsigned (fst s) + bv_unsigned (snd s).
Proof.
  intros z Hz.
  destruct (Z_lt_ge_dec z 77824) as [A|A].
  { exists (nth 0 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)). split; [apply cc_resv_nth; lia|].
    replace (bv_unsigned (fst (nth 0 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) with 65536 by (vm_compute; reflexivity).
    replace (bv_unsigned (snd (nth 0 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) with 12288 by (vm_compute; reflexivity).
    lia. }
  destruct (Z_lt_ge_dec z 135168) as [B|B].
  { exists (nth 1 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)). split; [apply cc_resv_nth; lia|].
    replace (bv_unsigned (fst (nth 1 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) with 77824 by (vm_compute; reflexivity).
    replace (bv_unsigned (snd (nth 1 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) with 57344 by (vm_compute; reflexivity).
    lia. }
  destruct (Z_lt_ge_dec z 143360) as [C|C].
  { exists (nth 2 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)). split; [apply cc_resv_nth; lia|].
    replace (bv_unsigned (fst (nth 2 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) with 135168 by (vm_compute; reflexivity).
    replace (bv_unsigned (snd (nth 2 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) with 8192 by (vm_compute; reflexivity).
    lia. }
  { exists (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)). split; [apply cc_resv_nth; lia|].
    replace (bv_unsigned (fst (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) with 143360 by (vm_compute; reflexivity).
    replace (bv_unsigned (snd (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) with 204800 by (vm_compute; reflexivity).
    lia. }
Qed.

(** A byte that is there and is not read-only is writable : the store bound holds. *)
Lemma cc_wview_of_mrd : forall segs m (x : word) b, mrd segs m x = Some b -> ro_addr segs x = false ->
  wview segs m x <> None.
Proof.
  intros segs m x b H R. unfold mrd in H. unfold wview. destruct (m x) as [b'|]; [discriminate|].
  unfold ro_addr in R. unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1 in H.
  destruct (find_segment segs (bv_unsigned x) 1) as [sg|]; [|discriminate].
  apply negb_false_iff in R. rewrite R. cbv iota. intros Hn.
  destruct (seg_readable sg); [|discriminate].
  change (N.to_nat 1) with 1%nat in H. cbn [segment_read_bytes] in H.
  rewrite Hn in H. discriminate.
Qed.

Lemma cc_wr_of_bytes : forall segs m a bs, bytes_at segs m a bs ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> ro_addr segs (wa (a + j)) = false) ->
  wr_at segs m a (Z.of_nat (length bs)).
Proof.
  intros segs m a bs HB HR. pose proof (bytes_at_bound segs m a bs HB) as Bd.
  split; [lia|]. split; [lia|]. intros j Hj.
  destruct HB as (_ & _ & H). pose proof (H (Z.to_nat j) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
  destruct (nth_error bs (Z.to_nat j)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  exact (cc_wview_of_mrd segs m _ b E (HR j Hj)).
Qed.

Lemma cc_rom_none : forall segs (x : word), find_segment segs (bv_unsigned x) 1 = None -> seg_rom segs x = None.
Proof. intros segs x H. unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite H. reflexivity. Qed.

Lemma cc_mrd_fs : forall segs m (x : word) b, MemNorm.task_mem segs m -> mrd segs m x = Some b ->
  find_segment segs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros segs m x b TM H. unfold mrd in H. destruct (m x) as [b'|] eqn:E; [exact (TM x b' E)|].
  left. intros Hn. rewrite (cc_rom_none segs x Hn) in H. discriminate.
Qed.

(** ** The conditions of the three branches *)
Lemma cc_sx32_b2z : forall b, sx32 (Z_to_bv 64 (b2z b)) = Z_to_bv 64 (b2z b).
Proof. intros [|]; reflexivity. Qed.

Lemma cc_eqb_b2z0 : forall b, bv_eqb (Z_to_bv 64 (b2z b)) (Z_to_bv 64 0) = negb b.
Proof. intros [|]; reflexivity. Qed.

Lemma cc_seqz_b2z : forall b, v_sltiu (Z_to_bv 64 (b2z b)) 1 = Z_to_bv 64 (b2z (negb b)).
Proof. intros [|]; reflexivity. Qed.

Lemma cc_land_b2z : forall a b,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (b2z a))) (bv_unsigned (Z_to_bv 64 (b2z b)))) =
  Z_to_bv 64 (b2z (a && b)).
Proof. intros [|] [|]; reflexivity. Qed.

(** `addi a0, a0, -4` then `seqz a0, a0` on a C int: the role is 4 (BOX). *)
Lemma cc_seqz_role : forall r, 0 <= r < 2^32 ->
  v_sltiu (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 r)) + -4)) 1 = Z_to_bv 64 (b2z (r =? 4)).
Proof.
  intros r Hr. unfold v_sltiu, sx32. rewrite (unsigned_lit r) by lia. rewrite !Z_to_bv_unsigned.
  destruct (Z.eqb_spec r 4) as [->|Hne]; [vm_compute; reflexivity|].
  match goal with |- (if ?b then _ else _) = _ => replace b with false end; [reflexivity|].
  symmetry. apply Z.ltb_ge. unfold bv_swrap, bv_half_modulus. unfold bv_wrap, bv_modulus.
  cbn [Z.of_N]. change (2 ^ 32 / 2) with (2 ^ 31). change (1 mod 2 ^ 64) with 1. Z.div_mod_to_equations. lia.
Qed.

Lemma cc_sx32_lit : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2^31). lia.
Qed.

Lemma cc_lts_lit : forall a b, 0 <= a < 2^63 -> 0 <= b < 2^63 -> bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt a (2^63))) by lia. rewrite (proj2 (Z.ltb_lt b (2^63))) by lia. reflexivity.
Qed.

(** ** The two formats in .rodata *)
Lemma cc_fmt_at : forall m (fp : Z) (f : list Z),
  mem_inv rsegs m -> ro_bytes_b rsegs fp (zb f ++ [ZERO]) = true -> 0 <= fp ->
  fp + Z.of_nat (length f) + 1 <= 2^64 -> existsb (Z.eqb 0) f = false -> zs (zb f) = f ->
  cstrz_at rsegs m fp f.
Proof.
  intros m fp f MI HB H0 H1 HZ HS. exists (zb f). split.
  - apply ro_bytes_at; [exact MI | lia | unfold zb; rewrite length_app, length_map; cbn [length]; lia |].
    apply ro_bytes_b_sound. exact HB.
  - split; [exact HS | apply cc_nz_of_existsb; exact HZ].
Qed.

Lemma cc_xmodel_len : Z.of_nat (length F_xmodel) = 103.
Proof. vm_compute. reflexivity. Qed.

Lemma cc_xbox_len : Z.of_nat (length F_xbox) = 91.
Proof. vm_compute. reflexivity. Qed.

Lemma cc_xmodel_at : forall m, mem_inv rsegs m -> cstrz_at rsegs m 66676 F_xmodel.
Proof.
  intros m MI. apply cc_fmt_at;
    [exact MI | vm_compute; reflexivity | lia | rewrite cc_xmodel_len; lia
     | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma cc_xbox_at : forall m, mem_inv rsegs m -> cstrz_at rsegs m 67253 F_xbox.
Proof.
  intros m MI. apply cc_fmt_at;
    [exact MI | vm_compute; reflexivity | lia | rewrite cc_xbox_len; lia
     | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma cc_in_xmodel : In F_xmodel REFUSE_FORMATS.
Proof. unfold REFUSE_FORMATS. cbn [In]. do 15 right. left. reflexivity. Qed.

Lemma cc_in_xbox : In F_xbox REFUSE_FORMATS.
Proof. unfold REFUSE_FORMATS. cbn [In]. do 16 right. left. reflexivity. Qed.

(** A writable byte is not read-only: what the stack region gives (stk). *)
Lemma cc_ro_of_wview : forall segs m (x : word), mem_inv segs m -> wview segs m x <> None ->
  ro_addr segs x = false.
Proof.
  intros segs m x MI W. destruct (m x) as [b|] eqn:E; [exact (MI x b E)|].
  unfold wview in W. rewrite E in W. unfold ro_addr.
  destruct (find_segment segs (bv_unsigned x) 1) as [sg|]; [|reflexivity].
  destruct (seg_writable sg) eqn:Ew; [reflexivity|]. exfalso. apply W. reflexivity.
Qed.

(** A string of a seg[] field is far shorter than printf's %s bound. *)
Lemma cc_le_65535 : forall n : nat, (n < 100)%nat -> (n <= 65535)%nat.
Proof. intros n H. apply Nat.le_trans with 100%nat; [lia | apply Nat.leb_le; vm_compute; reflexivity]. Qed.

Section Walk.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (c Sp lo : Z) (rc : rconf).
Hypothesis HREF : refuse_contract.
Hypothesis Hc : 0 < c.
Hypothesis Hc16 : c mod 16 = 0.
Hypothesis Hcb : c + 16616 <= 2^64.
Hypothesis HcA : c + 16616 <= lo \/ Sp <= c.
Hypothesis Hblk : blk_noimg rsegs c SEG_C_SIZE.
Hypothesis HRF : rc_refused rc + 64 < 2^32.
Hypothesis Hlo : 344200 <= lo.        (* sa_img_end SA *)
Hypothesis HK : lo + 6112 <= Sp.
Hypothesis HS : Sp < 2^63.
Hypothesis H16 : Sp mod 16 = 0.
Hypothesis HW : forall a, lo <= a < Sp -> seg_rom rsegs (wa a) = None.
Hypothesis HROS : forall x : word, lo <= bv_unsigned x < Sp -> ro_addr rsegs x = false.
Hypothesis HSSP : ssp_ok m0.
Hypothesis HTM : MemNorm.task_mem rsegs m0.
Hypothesis HMI : mem_inv rsegs m0.
Hypothesis HFC : frm0 fc.
Hypothesis HTW : forall z, (Sp - 6112 <= z < Sp \/ c <= z < c + 13520) ->
  find_segment rsegs z 1 <> None \/ z < TASK_SIZE.

(** The bytes cross_check may write: its frame (refuse's inside it), seg[32], refusal[8] with n_refusals and
    refused (cross_check_W). *)
Local Notation WCL := [(Sp - 6112, Sp); (c, c + 11392); (c + 11912, c + 13520)].

(** What holds of the memory between the prologue and the epilogue. *)
Definition frm (m : word -> option byte) : Prop :=
  rw_cells rsegs m (Sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (Sp + -80) /\ munch WCL m0 m /\ wmono rsegs m0 m.

(** What holds of the FP registers and of fcsr (refuse's callees write fa0 and the flags). *)
Definition fok (fc' : bv 32) (F' : bvmap 5 word) : Prop :=
  frm0 fc' /\ forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k.

Lemma cc_uc : bv_unsigned (Z_to_bv 64 c) = c.
Proof. apply unsigned_lit. lia. Qed.

Lemma cc_usp : bv_unsigned (Z_to_bv 64 (Sp + -80)) = Sp + -80.
Proof. apply unsigned_lit. lia. Qed.

Local Abbreviation Post := (ret_void_fp ra (Z_to_bv 64 Sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0
  WCL lo (fun m' => rconf_at rsegs m' c (cross_check rc))).

(** No byte of the block is in a segment of the image, so none of them is read-only and each is in m itself. *)
Lemma blk_fs : forall z, c <= z < c + 16616 -> find_segment rsegs z 1 = None.
Proof.
  intros z Hz. destruct (find_segment rsegs z 1) as [sg|] eqn:E; [exfalso|reflexivity].
  assert (H : find_segment rsegs z 1 <> None) by congruence.
  destruct (cc_resv_cover z (cc_fs_range z H)) as (s & Hin & Hb).
  apply (Hblk (z - c) ltac:(unfold SEG_C_SIZE; lia) s Hin). lia.
Qed.

Lemma blk_ro : forall x : word, c <= bv_unsigned x < c + 16616 -> ro_addr rsegs x = false.
Proof. intros x H. unfold ro_addr. rewrite (blk_fs _ H). reflexivity. Qed.

(** The block and the image are apart (both are intervals). *)
Lemma blk_apart_img : c + 16616 <= 65536 \/ 348160 <= c.
Proof.
  destruct (Z_le_gt_dec (c + 16616) 65536) as [L|L]; [left; exact L|right].
  destruct (Z_le_gt_dec 348160 c) as [R|R]; [exact R|exfalso].
  destruct (cc_resv_cover (Z.max c 65536) ltac:(lia)) as (s & Hin & Hb).
  apply (Hblk (Z.max c 65536 - c) ltac:(unfold SEG_C_SIZE; lia) s Hin). lia.
Qed.

Lemma cc_out_or_in : forall z, outside WCL z \/ (Sp - 6112 <= z < Sp \/ c <= z < c + 13520).
Proof.
  intros z. cbn [outside].
  destruct (Z_le_gt_dec (Sp - 6112) z), (Z_lt_ge_dec z Sp), (Z_le_gt_dec c z), (Z_lt_ge_dec z (c + 13520));
    try (right; lia); left; repeat split; try lia; exact I.
Qed.

Lemma frm_mi : forall m, frm m -> mem_inv rsegs m.
Proof.
  intros m (_ & _ & MU & _) x b Hx. destruct (cc_out_or_in (bv_unsigned x)) as [O|[O|O]].
  - rewrite (MU x O) in Hx. exact (HMI x b Hx).
  - apply HROS. lia.
  - apply blk_ro. lia.
Qed.

Lemma frm_tm : forall m, frm m -> MemNorm.task_mem rsegs m.
Proof.
  intros m (_ & _ & MU & _) x b Hx. destruct (cc_out_or_in (bv_unsigned x)) as [O|O].
  - rewrite (MU x O) in Hx. exact (HTM x b Hx).
  - exact (HTW _ O).
Qed.

Lemma frm_ssp : forall m, frm m -> ssp_ok m.
Proof.
  intros m (_ & _ & MU & _). destruct HSSP as [G1 [g G2]].
  pose proof blk_apart_img as AP.
  assert (D : forall a n, 65536 <= a -> a + n <= 344200 -> disjoint_from WCL a n).
  { intros a n H1 H2. cbn [disjoint_from]. repeat split; try lia; exact I. }
  split.
  - eapply bytes_at_transport; [exact G1 | exact MU |]. rewrite length_le8.
    apply D; vm_compute; discriminate.
  - exists g. eapply bytes_at_transport; [exact G2 | exact MU |]. rewrite length_le8.
    apply D; vm_compute; discriminate.
Qed.

Lemma frm_pe : forall m fc', frm m -> frm0 fc' -> printf_env m fc' lo (Sp + -80).
Proof.
  intros m fc' FRM FC. split; [exact FC|]. split; [exact (frm_tm m FRM)|].
  split; [exact (frm_ssp m FRM)|]. split; [exact Hlo | lia].
Qed.

Lemma frm_sok : forall m, frm m -> stack_ok rsegs m lo (Sp + -80) REFUSE_STACK.
Proof.
  intros m (_ & ST & _). split; [exact ST|].
  split; [unfold REFUSE_STACK, PRINTF_K; lia|].
  split; [Z.div_mod_to_equations; lia|].
  intros a Ha. apply HW. lia.
Qed.

(** The block is writable: every byte of it is there and no segment of it is read-only. *)
Lemma blk_wr : forall m bs, bytes_at rsegs m c bs -> Z.of_nat (length bs) = 16616 -> wr_at rsegs m c 16616.
Proof.
  intros m bs HB L. rewrite <- L. apply cc_wr_of_bytes; [exact HB|].
  intros j Hj. apply blk_ro. rewrite wa_unsigned by lia. lia.
Qed.

Lemma blk_sok : forall m bs off n, bytes_at rsegs m c bs -> Z.of_nat (length bs) = 16616 ->
  0 <= off -> off + Z.of_nat n <= 16616 -> store_ok rsegs m (wa (c + off)) n = true.
Proof.
  intros m bs off n HB L H0 H1. eapply wr_at_store_ok; [eapply blk_wr; eauto | lia | lia].
Qed.

(** A store inside seg[32]: the frame and the block after it. *)
Lemma blk_store : forall m bs off ws, frm m -> bytes_at rsegs m c bs -> Z.of_nat (length bs) = 16616 ->
  Z.of_nat off + Z.of_nat (length ws) <= 11392 ->
  frm (write_to_mem m (wa (c + Z.of_nat off)) ws) /\
  bytes_at rsegs (write_to_mem m (wa (c + Z.of_nat off)) ws) c (upd_bytes bs off ws).
Proof.
  intros m bs off ws (FR & ST & MU & WM) HB L Hoff.
  assert (Lw : Z.of_nat (length ws) <= 11392) by lia.
  split; [split; [|split; [|split]]|].
  - eapply rw_cells_frame; [exact FR | lia | lia |].
    cbn [cells_size csize Nat.add]. lia.
  - eapply stk_write; [exact ST | lia | lia].
  - eapply munch_write; [exact MU | lia | lia |]. cbn [inside]. right. left. lia.
  - apply wmono_write. exact WM.
  - pose proof (bytes_at_write_inside rsegs m c bs (Z.of_nat off) ws HB ltac:(lia) ltac:(lia)) as H.
    rewrite Nat2Z.id in H. exact H.
Qed.

(** refuse writes only inside cross_check's own footprint. *)
Lemma frm_refuse : forall m m' rc', frm m -> (length (rc_refusal rc') <= 8)%nat ->
  munch (refuse_W (Sp + -80) c rc') m m' -> wmono rsegs m m' -> stk rsegs m' lo (Sp + -80) -> frm m'.
Proof.
  intros m m' rc' (FR & ST & MU & WM) Hk MU' WM' ST'.
  assert (SUB : sub_fp (refuse_W (Sp + -80) c rc') WCL).
  { unfold sub_fp, refuse_W, REFUSE_STACK, PRINTF_K, RC_REFUSED, RC_NREF, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN.
    intros x Hx. cbn [outside app] in Hx |- *.
    destruct (length (rc_refusal rc') <? 8)%nat eqn:E; cbn [outside app] in *;
      [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E];
      repeat split; try lia; exact I. }
  split; [|split; [exact ST'|split]].
  - eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |].
    cbn [cells_size csize Nat.add].
    unfold refuse_W, REFUSE_STACK, PRINTF_K, RC_REFUSED, RC_NREF, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN.
    destruct (length (rc_refusal rc') <? 8)%nat eqn:E;
      [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]; cbn [disjoint_from app];
      repeat split; try lia; exact I.
  - eapply munch_trans; [exact MU | eapply munch_weaken; [exact SUB | exact MU']].
  - exact (wmono_trans rsegs _ _ _ WM WM').
Qed.

(** ** The two string arguments of a refusal: seg[i].name and seg[i].model *)
Lemma cc_fld_seg : forall (bs : list byte) i a n, (a + n <= 356)%nat ->
  fld a n (fld (356 * i) 356 bs) = fld (356 * i + a) n bs.
Proof.
  intros bs i a n H. unfold fld. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  rewrite Nat.min_l by lia. rewrite Nat.add_comm. reflexivity.
Qed.

Lemma cc_name_at : forall m bs rc' i, bytes_at rsegs m c bs -> rconf_enc rc' bs ->
  (i < length (rc_seg rc'))%nat ->
  cstr_at rsegs m (c + 356 * Z.of_nat i) (rs_name (nth i (rc_seg rc') rseg_d)) /\
  (length (rs_name (nth i (rc_seg rc') rseg_d)) < 16)%nat.
Proof.
  intros m bs rc' i HB HE Hi. pose proof HE as (L & LS & SEGS & _). unfold SEG_C_SIZE in L.
  destruct (SEGS i Hi) as (_ & NM & _). pose proof NM as (_ & Ls & _).
  rewrite cc_fld_seg in NM by lia. rewrite Nat.add_0_r in NM.
  split; [|exact Ls].
  replace (c + 356 * Z.of_nat i) with (c + Z.of_nat (356 * i)) by lia.
  eapply cc_cstr_in_block; [exact HB | exact NM | lia | lia].
Qed.

Lemma cc_model_at : forall m bs rc' i, bytes_at rsegs m c bs -> rconf_enc rc' bs ->
  (i < length (rc_seg rc'))%nat ->
  cstr_at rsegs m (c + 356 * Z.of_nat i + 36) (rs_model (nth i (rc_seg rc') rseg_d)) /\
  (length (rs_model (nth i (rc_seg rc') rseg_d)) < 24)%nat.
Proof.
  intros m bs rc' i HB HE Hi. pose proof HE as (L & LS & SEGS & _). unfold SEG_C_SIZE in L.
  destruct (SEGS i Hi) as (_ & _ & _ & _ & _ & _ & MO & _). pose proof MO as (_ & Ls & _).
  change (fldz RS_MODEL 24 ?x) with (fld 36 24 x) in MO.
  rewrite cc_fld_seg in MO by lia.
  split; [|exact Ls].
  replace (c + 356 * Z.of_nat i + 36) with (c + Z.of_nat (356 * i + 36)) by lia.
  eapply cc_cstr_in_block; [exact HB | exact MO | lia | lia].
Qed.

(** Both are apart from the stack, from the refusal slot and from c->refused. *)
Lemma cc_apart_arg : forall (a n : Z) (k : nat), c <= a -> a + n <= c + 11392 -> (k <= 8)%nat ->
  apart_all a n [(lo, Sp + -80); (refusal_addr c k, refusal_addr c k + RC_REFUSAL_LEN);
                 (c + RC_REFUSED, c + RC_REFUSED + 4)].
Proof.
  intros a n k H1 H2 H3. assert (Hk : Z.of_nat k <= 8) by lia.
  unfold refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_REFUSED, apart_all, apart.
  repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.

(** ** refuse's premise at the two call sites *)
Lemma pre_xmodel : forall m fc' bs i (z5 z6 z7 : word),
  frm m -> frm0 fc' -> bytes_at rsegs m c bs -> rconf_enc (rcs rc i) bs -> (i < length (rc_seg rc))%nat ->
  refuse_pre m fc' (bv_unsigned (Z_to_bv 64 (Sp + -80))) lo (bv_unsigned (Z_to_bv 64 c))
    (bv_unsigned (Z_to_bv 64 0)) (bv_unsigned (Z_to_bv 64 66676))
    [Z_to_bv 64 (c + 356 * Z.of_nat i); Z_to_bv 64 (c + 356 * Z.of_nat i + 36); z5; z6; z7]
    (rcs rc i) 0 F_xmodel
    [AS (rs_name (nth i (rc_seg (rcs rc i)) rseg_d)); AS (rs_model (nth i (rc_seg (rcs rc i)) rseg_d))].
Proof.
  intros m fc' bs i z5 z6 z7 FRM FC HB HE Hi.
  assert (Hi' : (i < length (rc_seg (rcs rc i)))%nat) by (rewrite rcs_len; exact Hi).
  pose proof HE as (HL & HLS & _ & _ & HLR & _).
  pose proof (rcs_refused rc i) as HRi.
  destruct (cc_name_at m bs (rcs rc i) i HB HE Hi') as [NA NL].
  destruct (cc_model_at m bs (rcs rc i) i HB HE Hi') as [MA ML].
  unfold SEG_C_SIZE in HL.
  assert (Hi32 : (i < 32)%nat) by (rewrite rcs_len in HLS; lia).
  rewrite !unsigned_lit by lia.
  unfold refuse_pre, RO_LO.
  split; [lia|]. split; [exact Hc16|]. split; [exists bs; split; assumption|].
  split; [unfold apart, SEG_C_SIZE; lia|]. split; [exact Hblk|].
  split; [lia|]. split; [lia|]. split; [reflexivity|].
  split; [exact cc_in_xmodel|]. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [apply cc_xmodel_at; exact (frm_mi m FRM)|].
  split; [lia|]. split; [rewrite cc_xmodel_len; vm_compute; discriminate|].
  split.
  { cbn [va_args_ok va_arg_ok].
    split; [|split; [|exact I]].
    - rewrite unsigned_lit by lia. split; [lia|]. split; [exact NA|]. split; [apply cc_le_65535; lia|].
      apply cc_apart_arg; lia.
    - rewrite unsigned_lit by lia. split; [lia|]. split; [exact MA|]. split; [apply cc_le_65535; lia|].
      apply cc_apart_arg; lia. }
  split; [exact (frm_pe m fc' FRM FC)|].
  split; [exact (frm_sok m FRM) | exact (frm_mi m FRM)].
Qed.

Lemma pre_xbox : forall m fc' bs i (z4 z5 z6 z7 : word),
  frm m -> frm0 fc' -> bytes_at rsegs m c bs -> rconf_enc (rcs rc i) bs -> (i < length (rc_seg rc))%nat ->
  refuse_pre m fc' (bv_unsigned (Z_to_bv 64 (Sp + -80))) lo (bv_unsigned (Z_to_bv 64 c))
    (bv_unsigned (Z_to_bv 64 0)) (bv_unsigned (Z_to_bv 64 67253))
    [Z_to_bv 64 (c + 356 * Z.of_nat i); z4; z5; z6; z7]
    (rcs rc i) 0 F_xbox [AS (rs_name (nth i (rc_seg (rcs rc i)) rseg_d))].
Proof.
  intros m fc' bs i z4 z5 z6 z7 FRM FC HB HE Hi.
  assert (Hi' : (i < length (rc_seg (rcs rc i)))%nat) by (rewrite rcs_len; exact Hi).
  pose proof HE as (HL & HLS & _ & _ & HLR & _).
  pose proof (rcs_refused rc i) as HRi.
  destruct (cc_name_at m bs (rcs rc i) i HB HE Hi') as [NA NL].
  unfold SEG_C_SIZE in HL.
  assert (Hi32 : (i < 32)%nat) by (rewrite rcs_len in HLS; lia).
  rewrite !unsigned_lit by lia.
  unfold refuse_pre, RO_LO.
  split; [lia|]. split; [exact Hc16|]. split; [exists bs; split; assumption|].
  split; [unfold apart, SEG_C_SIZE; lia|]. split; [exact Hblk|].
  split; [lia|]. split; [lia|]. split; [reflexivity|].
  split; [exact cc_in_xbox|]. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [apply cc_xbox_at; exact (frm_mi m FRM)|].
  split; [lia|]. split; [rewrite cc_xbox_len; vm_compute; discriminate|].
  split.
  { cbn [va_args_ok va_arg_ok].
    split; [|exact I].
    rewrite unsigned_lit by lia. split; [lia|]. split; [exact NA|]. split; [apply cc_le_65535; lia|].
    apply cc_apart_arg; lia. }
  split; [exact (frm_pe m fc' FRM FC)|].
  split; [exact (frm_sok m FRM) | exact (frm_mi m FRM)].
Qed.

(** ** One pass of the loop, 0x15f38 .. 0x15fa8 *)
Lemma pass : forall i m fc' F' (x1 y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 : word),
  (i < length (rc_seg rc))%nat -> frm m -> fok fc' F' -> rconf_at rsegs m c (rcs rc i) ->
  (forall m' fc'' F'' (x1' y0' y1' y2' z0' z1' z2' z3' z4' z5' z6' z7' u3' u4' u5' u6' : word),
     frm m' -> fok fc'' F'' -> rconf_at rsegs m' c (rcs rc (S i)) ->
     evt rsegs Post
       (MS (mkR x1' (Z_to_bv 64 (Sp + -80)) gp tp y0' y1' y2' (Z_to_bv 64 c)
                (Z_to_bv 64 (c + 356 * Z.of_nat i + 36)) z0' z1' z2' z3' z4' z5' z6' z7'
                (Z_to_bv 64 67253) (Z_to_bv 64 66676) (Z_to_bv 64 (c + 11392))
                (Z_to_bv 64 (356 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat i))
                (Z_to_bv 64 (18446744073709551615 - c)) (Z_to_bv 64 33) s9 s10 s11 u3' u4' u5' u6')
           F'' (Z_to_bv 64 0x15fa8) fc'' None m' (seg_rom rsegs))) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -80)) gp tp y0 y1 y2 (Z_to_bv 64 c) (Z_to_bv 64 (c + 356 * Z.of_nat i + 36))
             z0 z1 z2 z3 z4 z5 z6 z7 (Z_to_bv 64 67253) (Z_to_bv 64 66676) (Z_to_bv 64 (c + 11392))
             (Z_to_bv 64 (356 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat i))
             (Z_to_bv 64 (18446744073709551615 - c)) (Z_to_bv 64 33) s9 s10 s11 u3 u4 u5 u6)
        F' (Z_to_bv 64 0x15f38) fc' None m (seg_rom rsegs)).
Proof.
  intros i m fc' F' x1 y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 Hi FRM FOK RA K.
  destruct RA as (bs & HB & HE). pose proof FOK as (FC & FAG).
  assert (Hi' : (i < length (rc_seg (rcs rc i)))%nat) by (rewrite rcs_len; exact Hi).
  pose proof HE as (HL & HLS & _). unfold SEG_C_SIZE in HL.
  assert (Hi32 : (i < 32)%nat) by (rewrite rcs_len in HLS; lia).
  pose proof (cc_read_role_set rsegs m c bs (rcs rc i) i HB HE Hi') as RRS.
  destruct (cc_read_role rsegs m c bs (rcs rc i) i HB HE Hi') as [RB RRO].
  pose proof (cc_read_model_set rsegs m c bs (rcs rc i) i HB HE Hi') as RMS.
  (* the two UBSan checks of &c->seg[i]: i = 33, and c + 356 i wrapping *)
  step. rewrite cc_eqb_lit by lia.
  replace (Z.of_nat i =? 33) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. rewrite cc_ltu_lit by lia.
  replace (18446744073709551615 - c <? 356 * Z.of_nat i) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv iota.
  step. step. rewrite cc_sx32_b2z, cc_eqb_b2z0.
  destruct (rs_role_set (nth i (rc_seg (rcs rc i)) rseg_d)) eqn:ERS; cbn [negb]; cbv iota.
  - (* role_set *)
    step. step. step. rewrite cc_seqz_role by exact RB.
    step. step. step. rewrite cc_sx32_b2z, cc_eqb_b2z0.
    destruct (rs_model_set (nth i (rc_seg (rcs rc i)) rseg_d)) eqn:EMS; cbn [negb]; cbv iota.
    + (* model_set *)
      step. rewrite cc_eqb_b2z0.
      destruct (rs_role (nth i (rc_seg (rcs rc i)) rseg_d) =? 4) eqn:E4; cbn [negb]; cbv iota.
      * (* role = box: nothing to do *)
        step. rewrite cc_seqz_b2z. step. rewrite cc_land_b2z. step. rewrite cc_eqb_b2z0. cbn [andb negb]. cbv iota.
        apply K; [exact FRM | exact FOK |].
        rewrite rcs_S, (cc_cross_C (rcs rc i) i) by (rewrite ?ERS, ?EMS, ?E4; reflexivity).
        exists bs. split; assumption.
      * (* not box: refuse(c, 0, F_xmodel, name, model), then model[0] = 0 and model_set = 0 *)
        step. step. step. step. step.
        eapply evt_cut.
        { eapply HREF with (lo := lo) (ln := 0) (rc := rcs rc i) (f := F_xmodel)
            (args := [AS (rs_name (nth i (rc_seg (rcs rc i)) rseg_d));
                      AS (rs_model (nth i (rc_seg (rcs rc i)) rseg_d))]).
          eapply pre_xmodel; eassumption. }
        intros ms' PO.
        destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                        F'' & fc'' & m1 & -> & FC1 & FAG1 & MU1 & WM1 & MI1 & TM1 & ST1 & Q1).
        rewrite cc_uc in Q1. rewrite cc_uc, cc_usp in MU1. rewrite cc_usp in ST1.
        rewrite ret_pc_even by (try lia; reflexivity).
        assert (FRM1 : frm m1).
        { eapply frm_refuse; [exact FRM | | exact MU1 | exact WM1 | exact ST1].
          destruct HE as (_ & _ & _ & _ & HLR & _). lia. }
        assert (FOK1 : fok fc'' F'').
        { split; [exact FC1|]. intros k Hk. rewrite (FAG1 k Hk). apply FAG. exact Hk. }
        destruct Q1 as (bs1 & HB1 & HE1).
        pose proof HE1 as (HL1 & HLS1 & _). unfold SEG_C_SIZE in HL1.
        assert (HS1 : store_ok rsegs m1 (wa (c + (356 * Z.of_nat i + 36))) 1 = true)
          by (eapply blk_sok; [exact HB1 | lia | lia | lia]).
        replace (c + (356 * Z.of_nat i + 36)) with (c + 356 * Z.of_nat i + 36) in HS1 by lia.
        cbv beta delta [wa] in HS1.
        step.
        destruct (blk_store m1 bs1 (356 * i + 36) [ZERO] FRM1 HB1 ltac:(lia) ltac:(cbn [length]; lia))
          as [FRM2 HB2].
        replace (Z.of_nat (356 * i + 36)) with (356 * Z.of_nat i + 36) in FRM2, HB2 by lia.
        replace (c + (356 * Z.of_nat i + 36)) with (c + 356 * Z.of_nat i + 36) in FRM2, HB2 by lia.
        change (le1 (Z_to_bv 64 0)) with [ZERO].
        assert (HS2 : store_ok rsegs (write_to_mem m1 (wa (c + 356 * Z.of_nat i + 36)) [ZERO])
                        (wa (c + (356 * Z.of_nat i + 60))) 4 = true)
          by (eapply blk_sok; [exact HB2 | rewrite cc_upd_len; cbn [length]; lia | lia | lia]).
        replace (c + (356 * Z.of_nat i + 60)) with (c + 356 * Z.of_nat i + 60) in HS2 by lia.
        cbv beta delta [wa] in HS2.
        step.
        destruct (blk_store _ (upd_bytes bs1 (356 * i + 36) [ZERO]) (356 * i + 60) (le4 (Z_to_bv 64 0))
                    FRM2 HB2 ltac:(rewrite cc_upd_len; cbn [length]; lia) ltac:(rewrite length_le4; lia))
          as [FRM3 HB3].
        replace (Z.of_nat (356 * i + 60)) with (356 * Z.of_nat i + 60) in FRM3, HB3 by lia.
        replace (c + (356 * Z.of_nat i + 60)) with (c + 356 * Z.of_nat i + 60) in FRM3, HB3 by lia.
        step.
        apply K; [exact FRM3 | exact FOK1 |].
        exists (upd_bytes (upd_bytes bs1 (356 * i + 36) [ZERO]) (356 * i + 60) (le4 (Z_to_bv 64 0))).
        split; [exact HB3|].
        rewrite rcs_S, (cc_cross_A (rcs rc i) i) by (rewrite ?ERS, ?EMS, ?E4; reflexivity).
        apply cc_drop_model_rconf; [exact HE1|].
        destruct (refuse_proj (rcs rc i) 0 F_xmodel
                    [AS (rs_name (nth i (rc_seg (rcs rc i)) rseg_d));
                     AS (rs_model (nth i (rc_seg (rcs rc i)) rseg_d))]) as [Hsg _].
        rewrite Hsg. exact Hi'.
    + (* not model_set, role_set: is_box decides *)
      step. rewrite cc_seqz_b2z. step. rewrite cc_land_b2z. step. rewrite cc_eqb_b2z0. cbn [negb andb].
      destruct (rs_role (nth i (rc_seg (rcs rc i)) rseg_d) =? 4) eqn:E4; cbn [negb]; cbv iota.
      * (* box without a model: refuse(c, 0, F_xbox, name), then role = 0 and role_set = 0 *)
        step. step. step. step.
        eapply evt_cut.
        { eapply HREF with (lo := lo) (ln := 0) (rc := rcs rc i) (f := F_xbox)
            (args := [AS (rs_name (nth i (rc_seg (rcs rc i)) rseg_d))]).
          eapply pre_xbox; eassumption. }
        intros ms' PO.
        destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                        F'' & fc'' & m1 & -> & FC1 & FAG1 & MU1 & WM1 & MI1 & TM1 & ST1 & Q1).
        rewrite cc_uc in Q1. rewrite cc_uc, cc_usp in MU1. rewrite cc_usp in ST1.
        rewrite ret_pc_even by (try lia; reflexivity).
        assert (FRM1 : frm m1).
        { eapply frm_refuse; [exact FRM | | exact MU1 | exact WM1 | exact ST1].
          destruct HE as (_ & _ & _ & _ & HLR & _). lia. }
        assert (FOK1 : fok fc'' F'').
        { split; [exact FC1|]. intros k Hk. rewrite (FAG1 k Hk). apply FAG. exact Hk. }
        destruct Q1 as (bs1 & HB1 & HE1).
        pose proof HE1 as (HL1 & HLS1 & _). unfold SEG_C_SIZE in HL1.
        assert (HS1 : store_ok rsegs m1 (wa (c + (356 * Z.of_nat i + 16))) 4 = true)
          by (eapply blk_sok; [exact HB1 | lia | lia | lia]).
        replace (c + (356 * Z.of_nat i + 16)) with (c + 356 * Z.of_nat i + 16) in HS1 by lia.
        cbv beta delta [wa] in HS1.
        step.
        destruct (blk_store m1 bs1 (356 * i + 16) (le4 (Z_to_bv 64 0)) FRM1 HB1 ltac:(lia)
                    ltac:(rewrite length_le4; lia)) as [FRM2 HB2].
        replace (Z.of_nat (356 * i + 16)) with (356 * Z.of_nat i + 16) in FRM2, HB2 by lia.
        replace (c + (356 * Z.of_nat i + 16)) with (c + 356 * Z.of_nat i + 16) in FRM2, HB2 by lia.
        assert (HS2 : store_ok rsegs (write_to_mem m1 (wa (c + 356 * Z.of_nat i + 16)) (le4 (Z_to_bv 64 0)))
                        (wa (c + (356 * Z.of_nat i + 20))) 4 = true)
          by (eapply blk_sok; [exact HB2 | rewrite cc_upd_len; rewrite ?length_le4; lia | lia | lia]).
        replace (c + (356 * Z.of_nat i + 20)) with (c + 356 * Z.of_nat i + 20) in HS2 by lia.
        cbv beta delta [wa] in HS2.
        step.
        destruct (blk_store _ (upd_bytes bs1 (356 * i + 16) (le4 (Z_to_bv 64 0))) (356 * i + 20) (le4 (Z_to_bv 64 0))
                    FRM2 HB2 ltac:(rewrite cc_upd_len; rewrite ?length_le4; lia) ltac:(rewrite length_le4; lia))
          as [FRM3 HB3].
        replace (Z.of_nat (356 * i + 20)) with (356 * Z.of_nat i + 20) in FRM3, HB3 by lia.
        replace (c + (356 * Z.of_nat i + 20)) with (c + 356 * Z.of_nat i + 20) in FRM3, HB3 by lia.
        apply K; [exact FRM3 | exact FOK1 |].
        exists (upd_bytes (upd_bytes bs1 (356 * i + 16) (le4 (Z_to_bv 64 0))) (356 * i + 20) (le4 (Z_to_bv 64 0))).
        split; [exact HB3|].
        rewrite rcs_S, (cc_cross_B (rcs rc i) i) by (rewrite ?ERS, ?EMS, ?E4; reflexivity).
        apply cc_drop_role_rconf; [exact HE1|].
        destruct (refuse_proj (rcs rc i) 0 F_xbox [AS (rs_name (nth i (rc_seg (rcs rc i)) rseg_d))]) as [Hsg _].
        rewrite Hsg. exact Hi'.
      * (* neither *)
        apply K; [exact FRM | exact FOK |].
        rewrite rcs_S, (cc_cross_C (rcs rc i) i) by (rewrite ?ERS, ?EMS, ?E4; reflexivity). exists bs. split; assumption.
  - (* no role_set: is_box is false, so only the model branch can fire *)
    step. step. step. rewrite cc_sx32_b2z, cc_eqb_b2z0.
    destruct (rs_model_set (nth i (rc_seg (rcs rc i)) rseg_d)) eqn:EMS; cbn [negb]; cbv iota.
    + (* model_set without role_set: the xmodel refusal *)
      step. rewrite cc_eqb_b2z0. cbn [negb]. cbv iota.
      step. step. step. step. step.
      eapply evt_cut.
      { eapply HREF with (lo := lo) (ln := 0) (rc := rcs rc i) (f := F_xmodel)
          (args := [AS (rs_name (nth i (rc_seg (rcs rc i)) rseg_d));
                    AS (rs_model (nth i (rc_seg (rcs rc i)) rseg_d))]).
        eapply pre_xmodel; eassumption. }
      intros ms' PO.
      destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                      F'' & fc'' & m1 & -> & FC1 & FAG1 & MU1 & WM1 & MI1 & TM1 & ST1 & Q1).
      rewrite cc_uc in Q1. rewrite cc_uc, cc_usp in MU1. rewrite cc_usp in ST1.
      rewrite ret_pc_even by (try lia; reflexivity).
      assert (FRM1 : frm m1).
      { eapply frm_refuse; [exact FRM | | exact MU1 | exact WM1 | exact ST1].
        destruct HE as (_ & _ & _ & _ & HLR & _). lia. }
      assert (FOK1 : fok fc'' F'').
      { split; [exact FC1|]. intros k Hk. rewrite (FAG1 k Hk). apply FAG. exact Hk. }
      destruct Q1 as (bs1 & HB1 & HE1).
      pose proof HE1 as (HL1 & HLS1 & _). unfold SEG_C_SIZE in HL1.
      assert (HS1 : store_ok rsegs m1 (wa (c + (356 * Z.of_nat i + 36))) 1 = true)
        by (eapply blk_sok; [exact HB1 | lia | lia | lia]).
      replace (c + (356 * Z.of_nat i + 36)) with (c + 356 * Z.of_nat i + 36) in HS1 by lia.
      cbv beta delta [wa] in HS1.
      step.
      destruct (blk_store m1 bs1 (356 * i + 36) [ZERO] FRM1 HB1 ltac:(lia) ltac:(cbn [length]; lia))
        as [FRM2 HB2].
      replace (Z.of_nat (356 * i + 36)) with (356 * Z.of_nat i + 36) in FRM2, HB2 by lia.
      replace (c + (356 * Z.of_nat i + 36)) with (c + 356 * Z.of_nat i + 36) in FRM2, HB2 by lia.
      change (le1 (Z_to_bv 64 0)) with [ZERO].
      assert (HS2 : store_ok rsegs (write_to_mem m1 (wa (c + 356 * Z.of_nat i + 36)) [ZERO])
                      (wa (c + (356 * Z.of_nat i + 60))) 4 = true)
        by (eapply blk_sok; [exact HB2 | rewrite cc_upd_len; cbn [length]; lia | lia | lia]).
      replace (c + (356 * Z.of_nat i + 60)) with (c + 356 * Z.of_nat i + 60) in HS2 by lia.
      cbv beta delta [wa] in HS2.
      step.
      destruct (blk_store _ (upd_bytes bs1 (356 * i + 36) [ZERO]) (356 * i + 60) (le4 (Z_to_bv 64 0))
                  FRM2 HB2 ltac:(rewrite cc_upd_len; cbn [length]; lia) ltac:(rewrite length_le4; lia))
        as [FRM3 HB3].
      replace (Z.of_nat (356 * i + 60)) with (356 * Z.of_nat i + 60) in FRM3, HB3 by lia.
      replace (c + (356 * Z.of_nat i + 60)) with (c + 356 * Z.of_nat i + 60) in FRM3, HB3 by lia.
      step.
      apply K; [exact FRM3 | exact FOK1 |].
      exists (upd_bytes (upd_bytes bs1 (356 * i + 36) [ZERO]) (356 * i + 60) (le4 (Z_to_bv 64 0))).
      split; [exact HB3|].
      rewrite rcs_S, (cc_cross_A (rcs rc i) i) by (rewrite ?ERS, ?EMS, ?E4; reflexivity).
      apply cc_drop_model_rconf; [exact HE1|].
      destruct (refuse_proj (rcs rc i) 0 F_xmodel
                  [AS (rs_name (nth i (rc_seg (rcs rc i)) rseg_d));
                   AS (rs_model (nth i (rc_seg (rcs rc i)) rseg_d))]) as [Hsg _].
      rewrite Hsg. exact Hi'.
    + (* neither flag *)
      step. rewrite cc_seqz_b2z. step. rewrite cc_land_b2z. step. rewrite cc_eqb_b2z0. cbn [andb negb]. cbv iota.
      apply K; [exact FRM | exact FOK |].
      rewrite rcs_S, (cc_cross_C (rcs rc i) i) by (rewrite ?ERS, ?EMS, ?E4; reflexivity). exists bs. split; assumption.
Qed.

(** ** The epilogue, 0x15fbc *)
Lemma epi : forall m fc' F' (x1 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 w21 w22 w23 w24
                             y0 y1 y2 u3 u4 u5 u6 : word),
  frm m -> fok fc' F' -> rconf_at rsegs m c (cross_check rc) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -80)) gp tp y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 w21
             w22 w23 w24 s9 s10 s11 u3 u4 u5 u6)
        F' (Z_to_bv 64 0x15fbc) fc' None m (seg_rom rsegs)).
Proof.
  intros m fc' F' x1 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 w21 w22 w23 w24 y0 y1 y2 u3 u4 u5 u6
    FRM FOK Q.
  pose proof FRM as (FR & ST & MU & WM). pose proof FOK as (FC & FAG).
  do 12 step.
  apply evt_done. unfold ret_void_fp.
  exists y0, y1, y2, z0, z1, z2, z3, z4, z5, z6, z7, u3, u4, u5, u6, F', fc', m.
  split; [unfold mkR; repeat f_equal; lia|].
  split; [exact FC|]. split; [exact FAG|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact (frm_mi m FRM)|]. split; [exact (frm_tm m FRM)|].
  split; [|exact Q].
  rewrite unsigned_lit by lia.
  pose proof (stk_release rsegs m lo (Sp + -80) _ ST FR ltac:(lia)) as R.
  cbn [cells_size csize Nat.add] in R. replace (Sp + -80 + Z.of_nat 80) with Sp in R by lia. exact R.
Qed.

(** ** The loop, by induction on the entries left *)
Lemma loop : forall k i m fc' F' (x1 y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 : word),
  (i + k = length (rc_seg rc))%nat -> (0 < k)%nat -> frm m -> fok fc' F' -> rconf_at rsegs m c (rcs rc i) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -80)) gp tp y0 y1 y2 (Z_to_bv 64 c) (Z_to_bv 64 (c + 356 * Z.of_nat i + 36))
             z0 z1 z2 z3 z4 z5 z6 z7 (Z_to_bv 64 67253) (Z_to_bv 64 66676) (Z_to_bv 64 (c + 11392))
             (Z_to_bv 64 (356 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat i))
             (Z_to_bv 64 (18446744073709551615 - c)) (Z_to_bv 64 33) s9 s10 s11 u3 u4 u5 u6)
        F' (Z_to_bv 64 0x15f38) fc' None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH];
    intros i m fc' F' x1 y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 Hik Hk FRM FOK RA; [lia|].
  eapply pass; [lia | exact FRM | exact FOK | exact RA |].
  intros m' fc'' F'' x1' y0' y1' y2' z0' z1' z2' z3' z4' z5' z6' z7' u3' u4' u5' u6' FRM' FOK' RA'.
  pose proof RA' as (bs' & HB' & HE').
  pose proof (cc_read_n rsegs m' c bs' _ HB' HE') as RN. rewrite rcs_len in RN.
  pose proof HE' as (_ & HLS' & _). rewrite rcs_len in HLS'.
  do 5 step.
  rewrite cc_sx32_lit by lia. rewrite cc_lts_lit by lia.
  destruct (Z.ltb_spec (Z.of_nat i + 1) (Z.of_nat (length (rc_seg rc)))) as [LT|GE]; cbv iota.
  - replace (c + 356 * Z.of_nat i + 392) with (c + 356 * Z.of_nat (S i) + 36) by lia.
    replace (356 * Z.of_nat i + 356) with (356 * Z.of_nat (S i)) by lia.
    replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
    eapply (IH (S i)); [lia | lia | exact FRM' | exact FOK' | exact RA'].
  - eapply epi; [exact FRM' | exact FOK' |].
    replace (cross_check rc) with (rcs rc (S i)); [exact RA'|].
    unfold cross_check, rcs. f_equal. f_equal. lia.
Qed.

(** ** The whole function from its entry *)
Lemma body : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rconf_at rsegs m0 c rc -> stk rsegs m0 lo Sp ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CROSS_CHECK) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 RA ST.
  pose proof loop as LP. pose proof epi as EP.
  destruct RA as (bs & HB & HE).
  pose proof HE as (HL & HLS & _). unfold SEG_C_SIZE in HL.
  pose proof (munch_refl WCL m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 80 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 80) with 80 in ST1, FR.
  replace (Sp - 80) with (Sp + -80) in ST1, FR by lia.
  unfold CROSS_CHECK.
  do 12 step.
  (* UBSan: c <> 0, then c is 8-aligned *)
  rewrite cc_eqb_lit by lia. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step.
  rewrite (cc_land7 (bv_unsigned (Z_to_bv 64 c))) by (rewrite unsigned_lit by lia; lia).
  step. rewrite cc_eqb_lit by lia. change (negb (0 =? 0)) with false. cbv iota.
  do 3 step.
  pose proof (cc_read_n rsegs _ c bs rc HB HE) as RN.
  step. step.
  rewrite cc_sx32_lit by lia. rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (Z.of_nat (length (rc_seg rc)) <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite andb_true_r.
  destruct (Z.ltb_spec 0 (Z.of_nat (length (rc_seg rc)))) as [P|P]; cbn [negb]; cbv iota.
  - do 9 step.
    rewrite (unsigned_lit c) by lia. rewrite zb_lxor_ones by lia.
    replace (c + 36) with (c + 356 * Z.of_nat 0 + 36) by lia.
    eapply (LP (length (rc_seg rc)) 0%nat); [lia | lia | | |].
    + refine (conj _ (conj _ (conj _ _))); eassumption.
    + split; [exact HFC | intros k Hk; reflexivity].
    + exists bs. split; assumption.
  - eapply EP.
    + refine (conj _ (conj _ (conj _ _))); eassumption.
    + split; [exact HFC | intros k Hk; reflexivity].
    + exists bs. split; [exact HB|].
      replace (cross_check rc) with rc; [exact HE|].
      unfold cross_check. destruct (rc_seg rc) as [|x l] eqn:Es; [reflexivity|]. cbn [length] in P. lia.
Qed.

End Walk.

(** ** The theorem *)
Theorem cross_check_holds : refuse_contract -> cross_check_contract.
Proof.
  intros HREF. unfold cross_check_contract, cross_check_pre, CROSS_CHECK_STACK, REFUSE_STACK, PRINTF_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo rc
    (Hc0 & Hcm & RA & HcAp & Hblk & HRF & PE & SO & MI).
  destruct PE as (HFC & HTM & HSSP & HLO & HSP).
  destruct SO as (ST & HKK & H16 & HWW).
  change (sa_img_end SA) with 344200 in HLO.
  pose proof RA as (bs & HB & HE). pose proof HE as (HL & _). unfold SEG_C_SIZE in HL.
  pose proof (bytes_at_bound _ _ _ _ HB) as Bd.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  unfold apart, SEG_C_SIZE in HcAp.
  (* the two facts about the addresses of W that the walk needs *)
  assert (HROS : forall x : word, lo <= bv_unsigned x < bv_unsigned sp -> ro_addr rsegs x = false).
  { intros x Hx. destruct ST as (_ & _ & STa). destruct (STa (bv_unsigned x) Hx) as [Wv _].
    rewrite Z_to_bv_lit_self in Wv. exact (cc_ro_of_wview rsegs m x MI Wv). }
  assert (HTW : forall z, (bv_unsigned sp - 6112 <= z < bv_unsigned sp \/
                           bv_unsigned a0 <= z < bv_unsigned a0 + 13520) ->
                find_segment rsegs z 1 <> None \/ z < TASK_SIZE).
  { intros z [Hz|Hz].
    - destruct ST as (_ & _ & STa). destruct (STa z ltac:(lia)) as [_ (b & Hb)].
      pose proof (cc_mrd_fs rsegs m (wa z) b HTM Hb) as H. rewrite wa_unsigned in H by lia. exact H.
    - destruct HB as (_ & _ & HBi). pose proof (HBi (Z.to_nat (z - bv_unsigned a0)) ltac:(lia)) as E.
      destruct (nth_error bs (Z.to_nat (z - bv_unsigned a0))) as [b|] eqn:Eb;
        [|apply nth_error_None in Eb; lia].
      rewrite Z2Nat.id in E by lia.
      replace (bv_unsigned a0 + (z - bv_unsigned a0)) with z in E by lia.
      pose proof (cc_mrd_fs rsegs m (wa z) b HTM E) as H. rewrite wa_unsigned in H by lia. exact H. }
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  set (Sp := bv_unsigned sp) in *. set (c := bv_unsigned a0) in *.
  rewrite <- Esp, <- Ea0. clearbody Sp c. clear Esp Ea0.
  eapply (body ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m c Sp lo rc HREF);
    try eassumption; try lia.
Qed.
