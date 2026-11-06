(** reac_declared_vlan_split (UBSan build, 0x16338): proof of [reac_declared_vlan_split_contract]
    (U/Prog/reac_declared_vlan_split_c.v) from the contracts of its five callees (strrchr, strtol with a NULL
    end pointer, strlen, memcpy, name_ok). Written new; the plain walk is
    lib/Prog/reac_declared_vlan_split.v.

    Code (the UBSan binary):
      0x16338-0x16354  frame of 64: ra s0 s1 s2 s3 s4 s5 at sp+0x38 .. sp+8 (sp+0 unused)
      0x16358-0x16378  s2 = segment, s1 = parent, s3 = cap, s0 = vid, four `beqz` to the epilogue
      0x1637c-0x16384  strrchr(segment, '.'); 0x16388 s4 = dot
      0x16390 beqz s4; 0x16394 beq s4,s2; 0x1639c beq s4,-1 -> TRAP; 0x163a4 lbu a4,0(dot+1); beqz a4
      LOOP 0x163b8 addi a4,a4,-0x30; bltu a1,a4 -> 0x163f4; 0x163c0 beq a3,-1 -> TRAP;
           lbu a4,1(a3); addi a3,a3,1; bnez a4 -> LOOP
      0x163d0 a2 = 10; 0x163d4 a1 = 0; 0x163d8 strtol(dot + 1, NULL, 10); 0x163dc s5 = v
      0x163f0 bgeu (v - 4095), -4094 -> 0x1641c, else 0x163f4 (a0 = 0) and the epilogue
      0x1641c s4 = plen; 0x16428 bltu cap,plen+1; 0x16430 bltu 16,plen+1; 0x16438 strlen(segment)
      0x16444 bltu (len - 16), -17 -> 0x163f4; 0x16454 memcpy(parent, segment, plen)
      0x1645c bltu ~parent,plen -> TRAP; 0x16464 sb zero,0(parent+plen); 0x1646c name_ok(parent)
      0x16470 beqz a0 -> epilogue; 0x16478 bnez (vid & 1) -> TRAP; 0x1647c sh s5,0(vid); a0 = 1
      EPI 0x163f8 restore ra s0-s5; addi sp,sp,0x40; ret.  TRAP 0x16488 unimp
    The four traps are dead: dot and the loop's p are bytes of the segment, below segment + length s, and
    bytes_at bounds that by 2^64; parent + plen <= parent + 16 <= 2^64; vid is 2-aligned (vid mod 2 = 0).
    The digit loop is an induction on the bytes left before the NUL ([dloop]); every other block is
    straight-line. The model side is SegModel.vlan_split, through U/Spec/SegBridge.v and
    seg_tok_bridge.cstr_cut. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame
  Tac ZBridge Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_tok_bridge
  seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env __intscan_c strtol_c
  strrchr_c strtol_null_c strlen_c memcpy_c name_ok_c reac_declared_vlan_split_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Context-free helpers

    [apart] stays folded in every hypothesis of this walk: it is a disjunction, and [lia] case-splits the whole
    context. These lemmas take the disjunctions apart in a context of their own. *)

Lemma apt_sub : forall (A n L Hi a b n' : Z), apart A n L Hi -> L <= a -> b <= Hi -> n' <= n -> apart A n' a b.
Proof. unfold apart. intros. lia. Qed.

Lemma apt_dis1 : forall (A n a b : Z), apart A n a b -> disjoint_from [(a, b)] A n.
Proof. unfold apart. intros A n a b Hd. cbn [disjoint_from]. split; [exact Hd | exact I]. Qed.

Lemma apt_dis2 : forall (A n a b c d : Z), apart A n a b -> apart A n c d -> disjoint_from [(a, b); (c, d)] A n.
Proof.
  unfold apart. intros A n a b c d H1 H2. cbn [disjoint_from].
  split; [exact H1 | split; [exact H2 | exact I]].
Qed.

Lemma apt_or : forall (A n a b : Z), apart A n a b -> A + n <= a \/ b <= A.
Proof. unfold apart. intros A n a b H. exact H. Qed.

(** A footprint grows: what munched inside W munched inside W ++ R. *)
Lemma sub_fp_app : forall (W R : list ivl) (x : Z), outside (W ++ R) x -> outside W x.
Proof.
  intros W. induction W as [|[a b] W IH]; intros R x H; cbn [app outside] in *; [exact I|].
  destruct H as [H1 H2]. split; [exact H1 | apply (IH R x H2)].
Qed.

Lemma munch_pref : forall (W R : list ivl) (m m' : word -> option byte), munch W m m' -> munch (W ++ R) m m'.
Proof.
  intros W R m m' H. eapply munch_weaken; [| exact H].
  unfold sub_fp. intros x. apply sub_fp_app.
Qed.

Lemma bat_pre : forall segs m a (l1 l2 : list byte), bytes_at segs m a (l1 ++ l2) -> bytes_at segs m a l1.
Proof. intros segs m a l1 l2 H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma bat_suf : forall segs m a (l1 l2 : list byte),
  bytes_at segs m a (l1 ++ l2) -> bytes_at segs m (a + Z.of_nat (length l1)) l2.
Proof. intros segs m a l1 l2 H. apply bytes_at_app in H. exact (proj2 H). Qed.

Lemma wr_at_le : forall segs m A n j, wr_at segs m A n -> 0 <= j <= n -> wr_at segs m A j.
Proof.
  intros segs m A n j (H0 & H1 & H2) Hj. split; [exact H0|]. split; [lia|]. intros i Hi. apply H2. lia.
Qed.

Lemma wr_at_shift : forall segs m A n k j, wr_at segs m A n -> 0 <= k -> 0 <= j -> k + j <= n ->
  wr_at segs m (A + k) j.
Proof.
  intros segs m A n k j (H0 & H1 & H2) Hk Hj Hkj. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply H2. lia.
Qed.

(** One [CB n] block split at k: what the memcpy destination and the NUL after it need. *)
Lemma rw_cb_split : forall segs m A n k (bts : list byte),
  rw_cells segs m A [CB n bts] -> (k <= n)%nat ->
  rw_cells segs m A [CB k (firstn k bts)] /\
  rw_cells segs m (A + Z.of_nat k) [CB (n - k) (skipn k bts)].
Proof.
  intros segs m A n k bts [[Hwf Hb] Hw] Hk.
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  rewrite <- (firstn_skipn k bts) in Hb. apply bytes_at_app in Hb. destruct Hb as [H1 H2].
  rewrite length_firstn in H2. rewrite Nat.min_l in H2 by lia.
  split.
  - split.
    + split.
      * cbn [cells_wf cell_wf]. split; [rewrite length_firstn; lia | exact I].
      * cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H1.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. eapply wr_at_le; [exact Hw | lia].
  - split.
    + split.
      * cbn [cells_wf cell_wf]. split; [rewrite length_skipn; lia | exact I].
      * cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H2.
    + cbn [cells_size csize]. rewrite Nat.add_0_r.
      eapply wr_at_shift; [exact Hw | lia | lia | lia].
Qed.

(** The digit test the loop uses: `a1 - 0x30 >u 9`. *)
Lemma dig_no : forall v, 0 <= v < 256 -> 9 < (v + -48) mod 2 ^ 64 -> isdigit v = false.
Proof.
  intros v Hv H. unfold isdigit. destruct (Z.leb_spec 48 v) as [Hc|Hc]; cbn [andb].
  - rewrite (Z.mod_small (v + -48) (2 ^ 64)) in H by lia.
    destruct (Z.leb_spec v 57) as [Hd|Hd]; [exfalso; lia | reflexivity].
  - reflexivity.
Qed.

Lemma dig_yes : forall v, 0 <= v < 256 -> (v + -48) mod 2 ^ 64 <= 9 -> isdigit v = true.
Proof.
  intros v Hv H. unfold isdigit. destruct (Z.leb_spec 48 v) as [Hc|Hc]; cbn [andb].
  - rewrite (Z.mod_small (v + -48) (2 ^ 64)) in H by lia.
    destruct (Z.leb_spec v 57) as [Hd|Hd]; [reflexivity | exfalso; lia].
  - exfalso. assert (E : (v + -48) mod 2 ^ 64 = 2 ^ 64 + v - 48).
    { replace (v + -48) with (2 ^ 64 + v - 48 + (-1) * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    rewrite E in H. lia.
Qed.

(** The range test `v - 4095 >=u -4094`. *)
Lemma rng_in : forall v, 0 <= v < 2 ^ 63 -> (-4094) mod 2 ^ 64 <= (v + -4095) mod 2 ^ 64 -> 1 <= v <= 4094.
Proof.
  intros v Hv H.
  assert (E1 : (-4094) mod 2 ^ 64 = 2 ^ 64 - 4094) by (vm_compute; reflexivity).
  rewrite E1 in H.
  destruct (Z.le_gt_cases 4095 v) as [Hc|Hc].
  - rewrite (Z.mod_small (v + -4095) (2 ^ 64)) in H by lia. lia.
  - assert (E2 : (v + -4095) mod 2 ^ 64 = 2 ^ 64 + v - 4095).
    { replace (v + -4095) with (2 ^ 64 + v - 4095 + (-1) * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    rewrite E2 in H. lia.
Qed.

Lemma rng_out : forall v, 0 <= v < 2 ^ 63 -> (v + -4095) mod 2 ^ 64 < (-4094) mod 2 ^ 64 ->
  ((v <? 1) || (4094 <? v))%bool = true.
Proof.
  intros v Hv H.
  assert (E1 : (-4094) mod 2 ^ 64 = 2 ^ 64 - 4094) by (vm_compute; reflexivity).
  rewrite E1 in H.
  destruct (Z.le_gt_cases 4095 v) as [Hc|Hc].
  - apply orb_true_intro. right. apply Z.ltb_lt. lia.
  - assert (E2 : (v + -4095) mod 2 ^ 64 = 2 ^ 64 + v - 4095).
    { replace (v + -4095) with (2 ^ 64 + v - 4095 + (-1) * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    rewrite E2 in H. apply orb_true_intro. left. apply Z.ltb_lt. lia.
Qed.

(** `strlen(segment) - 16 <u -17` is false for a string shorter than 16 bytes. *)
Lemma len_test : forall n, 0 <= n < 16 -> ((n + -16) mod 2 ^ 64 <? (-17) mod 2 ^ 64) = false.
Proof.
  intros n Hn. apply Z.ltb_ge.
  assert (E1 : (-17) mod 2 ^ 64 = 2 ^ 64 - 17) by (vm_compute; reflexivity).
  assert (E2 : (n + -16) mod 2 ^ 64 = 2 ^ 64 + n - 16).
  { replace (n + -16) with (2 ^ 64 + n - 16 + (-1) * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite E1, E2. lia.
Qed.

(** Byte and list facts. *)
Lemma byte_nz : forall c : byte, c <> ZERO -> bv_unsigned c <> 0.
Proof. intros c Hc E. apply Hc. apply bv_eq. rewrite E. reflexivity. Qed.

Lemma zxb_zero : zxb ZERO = Z_to_bv 64 0.
Proof. apply bv_eq. reflexivity. Qed.

(** The UBSan pointer-overflow checks compare against -1. *)
Lemma eqb_m1 : forall z, 0 <= z < 2 ^ 64 - 1 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 (-1)) = false.
Proof.
  intros z Hz. unfold bv_eqb. rewrite (unsigned_lit z) by lia. rewrite unsigned_lit_wrap.
  assert (E : (-1) mod 2 ^ 64 = 2 ^ 64 - 1) by (vm_compute; reflexivity).
  rewrite E. apply Z.eqb_neq. lia.
Qed.

(** `not a0, s1`, as the step leaves it. *)
Lemma not_val : forall c, 0 <= c < 2 ^ 64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 c)) 18446744073709551615))
  = 18446744073709551615 - c.
Proof.
  intros c Hc. rewrite (unsigned_lit c) by lia. rewrite zb_lxor_ones by lia. apply unsigned_lit. lia.
Qed.

(** `andi a0, s0, 1` is the low bit. *)
Lemma land1 : forall x, 0 <= x -> Z.land x 1 = x mod 2.
Proof. intros x Hx. change 1 with (2 ^ 1 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

(** The byte `sb zero` writes. *)
Lemma le1_zero : le1 (Z_to_bv 64 0) = [ZERO].
Proof. rewrite <- zxb_zero. apply le1_zxb. Qed.

Lemma zs_firstn : forall k (l : list byte), zs (firstn k l) = firstn k (zs l).
Proof.
  unfold zs. intros k. induction k as [|k IH]; intros [|x l]; cbn [map firstn]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma zs_skipn : forall k (l : list byte), zs (skipn k l) = skipn k (zs l).
Proof.
  unfold zs. intros k. induction k as [|k IH]; intros [|x l]; cbn [map skipn]; try reflexivity.
  apply IH.
Qed.

Lemma in_skipn : forall {A : Type} k (l : list A) x, In x (skipn k l) -> In x l.
Proof.
  induction k as [|k IH]; intros [|y l] x H; cbn [skipn] in *; try tauto.
  right. apply (IH l x H).
Qed.

Lemma in_firstn : forall {A : Type} k (l : list A) x, In x (firstn k l) -> In x l.
Proof.
  induction k as [|k IH]; intros [|y l] x H; cbn [firstn In] in *; try tauto.
  destruct H as [H|H]; [left; exact H | right; apply (IH l x H)].
Qed.

Section Split.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (Sp lo TP segment parent vid : Z) (s : list Z) (ev : word)
  (bs sl pb : list byte).

Hypothesis HSRCH : strrchr_contract.
Hypothesis HSTOL : strtol_null_contract.
Hypothesis HSLEN : strlen_contract.
Hypothesis HMCPY : memcpy_contract.
Hypothesis HNOK : name_ok_contract.
Hypothesis Etp : bv_unsigned tp = TP.
(** The segment, cut to the slack strrchr and strlen read (seg_tok_bridge.cstr_cut). *)
Hypothesis HB0 : bytes_at rsegs m0 segment (bs ++ ZERO :: sl).
Hypothesis HZB : zs bs = s.
Hypothesis HNN : ~ In 0 s.
Hypothesis HNZ : ~ In ZERO bs.
Hypothesis HLB : length bs = length s.
Hypothesis HSK : (- (segment + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length sl).
Hypothesis HSL8 : Z.of_nat (length sl) < 8.
Hypothesis Hseg : 0 < segment.
Hypothesis Hlen : (length s < 16)%nat.
Hypothesis Hsegb : segment + Z.of_nat (length s) + 8 <= 2 ^ 64.
Hypothesis HsegA : apart segment (Z.of_nat (length s) + 8) lo Sp.
Hypothesis Hpar : 0 < parent.
Hypothesis HPB : rw_cells rsegs m0 parent [CB 16 pb].
Hypothesis HparA : apart parent 16 lo Sp.
Hypothesis HsegP : apart segment (Z.of_nat (length s) + 8) parent (parent + 16).
Hypothesis Hvid : 0 < vid.
Hypothesis Hvid2 : vid mod 2 = 0.
Hypothesis HWV : wr_at rsegs m0 vid 2.
Hypothesis HvidA : apart vid 2 lo Sp.
Hypothesis HvidP : apart vid 2 parent (parent + 16).
Hypothesis HEC : rw_cells rsegs m0 (TP - 164) [C4 ev].
Hypothesis HecA : apart (TP - 164) 4 lo Sp.
Hypothesis HecG : apart (TP - 164) 4 (sa_guard SA) (sa_guard SA + 8).
Hypothesis HecS : apart (TP - 164) 4 segment (segment + Z.of_nat (length s) + 8).
Hypothesis HecP : apart (TP - 164) 4 parent (parent + 16).
Hypothesis HecV : apart (TP - 164) 4 vid (vid + 2).
Hypothesis HGOT : bytes_at rsegs m0 (sa_got_guard SA) (le8 (Z_to_bv 64 (sa_guard SA))).
Hypothesis HGRD : exists g : word, bytes_at rsegs m0 (sa_guard SA) (le8 g).
Hypothesis Himg : sa_img_end SA <= lo.
Hypothesis HST : stk rsegs m0 lo Sp.
Hypothesis HKD : lo + 432 <= Sp.
Hypothesis HSp16 : Sp mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < Sp -> seg_rom rsegs (wa a) = None.
Hypothesis HMI : mem_inv rsegs m0.
Hypothesis HSpb : Sp < 2 ^ 64.
Hypothesis Hlo0 : 0 <= lo.
Hypothesis HTPr : 0 <= TP < 2 ^ 64.

(** The image cells strtol reads lie below [lo]. *)
Lemma got_lo : sa_got_guard SA + 8 <= lo.
Proof. assert (K : sa_got_guard SA + 8 <= sa_img_end SA) by (vm_compute; discriminate). lia. Qed.

Lemma grd_lo : sa_guard SA + 8 <= lo.
Proof. assert (K : sa_guard SA + 8 <= sa_img_end SA) by (vm_compute; discriminate). lia. Qed.

(** Bounds of the objects. *)
Lemma par_b : 0 <= parent /\ parent + 16 <= 2 ^ 64.
Proof. pose proof (rw_cells_bound rsegs m0 parent _ HPB) as H. cbn [cells_size csize] in H. lia. Qed.

Lemma vid_b : vid + 2 <= 2 ^ 64.
Proof. destruct HWV as (_ & H & _). lia. Qed.

Lemma seg_b : segment + Z.of_nat (length bs) + 1 + Z.of_nat (length sl) <= 2 ^ 64.
Proof.
  pose proof (bytes_at_bound _ _ _ _ HB0) as H. rewrite length_app in H. cbn [length] in H. lia.
Qed.

(** strtol's stack-protector guard is apart from the errno cell (the premise stated in strtol's own names). *)
Lemma ec_guard : STRTOL_SSP_GUARD + 8 <= TP - 164 \/ TP - 164 + 4 <= STRTOL_SSP_GUARD.
Proof.
  pose proof (apt_or _ _ _ _ HecG) as K. change (sa_guard SA) with STRTOL_SSP_GUARD in K. lia.
Qed.

(** The footprint everything but the memcpy stays inside: the stack region and the errno cell. *)
Local Notation WB := ([(Sp - 432, Sp); (TP - 164, TP - 164 + 4)]).

(** ** Carrying the caller's objects over a callee that writes only inside the stack region *)

Lemma tr_seg : forall m, munch [(Sp - 432, Sp)] m0 m -> bytes_at rsegs m segment (bs ++ ZERO :: sl).
Proof.
  intros m MU. eapply bytes_at_transport; [exact HB0 | exact MU |].
  apply apt_dis1. eapply apt_sub; [exact HsegA | lia | lia |].
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma tr_seg2 : forall m, munch WB m0 m -> bytes_at rsegs m segment (bs ++ ZERO :: sl).
Proof.
  intros m MU. eapply bytes_at_transport; [exact HB0 | exact MU |].
  apply apt_dis2.
  - eapply apt_sub; [exact HsegA | lia | lia |]. rewrite length_app; cbn [length]; lia.
  - unfold apart in HecS |- *. rewrite length_app; cbn [length]; lia.
Qed.

Lemma tr_par : forall m, munch [(Sp - 432, Sp)] m0 m -> wmono rsegs m0 m -> rw_cells rsegs m parent [CB 16 pb].
Proof.
  intros m MU WM. eapply rw_cells_transport; [exact HPB | exact MU | exact WM |].
  cbn [cells_size csize]. rewrite Nat.add_0_r.
  apply apt_dis1. eapply apt_sub; [exact HparA | lia | lia | lia].
Qed.

Lemma tr_par2 : forall m, munch WB m0 m -> wmono rsegs m0 m -> rw_cells rsegs m parent [CB 16 pb].
Proof.
  intros m MU WM. eapply rw_cells_transport; [exact HPB | exact MU | exact WM |].
  cbn [cells_size csize]. rewrite Nat.add_0_r.
  apply apt_dis2.
  - eapply apt_sub; [exact HparA | lia | lia | lia].
  - unfold apart in HecP |- *. lia.
Qed.

Lemma tr_vid : forall m, wmono rsegs m0 m -> wr_at rsegs m vid 2.
Proof. intros m WM. eapply wr_at_transport; [exact HWV | exact WM]. Qed.

(** Carrying the errno cell over a callee or a store that misses it. *)
Lemma tr_ec_mv : forall (m m' : word -> option byte) (W : list ivl),
  rw_cells rsegs m (TP - 164) [C4 ev] -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W (TP - 164) 4 -> rw_cells rsegs m' (TP - 164) [C4 ev].
Proof.
  intros m m' W H MU WM D. eapply rw_cells_transport; [exact H | exact MU | exact WM |].
  cbn [cells_size csize]. exact D.
Qed.

(** The contract's footprint on the three kinds of exit. *)
Lemma mw_none : forall m, split_copy s = None -> vlan_split s = None ->
  munch [(Sp - 432, Sp)] m0 m -> munch (split_W Sp TP parent vid s) m0 m.
Proof.
  intros m H1 H2 MU. unfold split_W, SPLIT_STACK. rewrite H1, H2. cbn [app].
  eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside].
  intros x (Hx1 & Hx2 & _). split; [lia | exact I].
Qed.

Lemma mw_copy : forall m di, split_copy s = Some di -> vlan_split s = None ->
  munch [(Sp - 432, Sp); (TP - 164, TP - 164 + 4); (parent, parent + Z.of_nat di + 1)] m0 m ->
  munch (split_W Sp TP parent vid s) m0 m.
Proof.
  intros m di H1 H2 MU. unfold split_W, SPLIT_STACK. rewrite H1, H2. cbn [app].
  eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside].
  intros x (Hx1 & Hx2 & Hx3 & _). split; [lia | split; [lia | split; [lia | exact I]]].
Qed.

Lemma mw_full : forall m di p v, split_copy s = Some di -> vlan_split s = Some (p, v) ->
  munch [(Sp - 432, Sp); (TP - 164, TP - 164 + 4); (parent, parent + Z.of_nat di + 1);
         (vid, vid + 2)] m0 m ->
  munch (split_W Sp TP parent vid s) m0 m.
Proof.
  intros m di p v H1 H2 MU. unfold split_W, SPLIT_STACK. rewrite H1, H2. cbn [app].
  eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside].
  intros x (Hx1 & Hx2 & Hx3 & Hx4 & _).
  split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]].
Qed.

(** The spine's answer, with the two length tests the compiled code also makes settled: [di < length s < 16]
    makes `plen + 1 >u 16` and `strlen(segment) >= 16` both false, and the segment has no NUL, so the tail the
    model cuts at the NUL is the whole tail. *)
Lemma vs_unfold : forall di, strrchr s DOT = Some di -> (di < length s)%nat ->
  vlan_split s =
    (if (di =? 0)%nat || (hd0 (skipn (S di) s) =? 0) then None else
     if negb (forallb isdigit (skipn (S di) s)) then None else
     if (strtol10 (skipn (S di) s) <? 1) || (4094 <? strtol10 (skipn (S di) s)) then None else
     if negb (name_ok (firstn di s)) then None else
     Some (firstn di s, strtol10 (skipn (S di) s) mod 65536)).
Proof.
  intros di HD Hdi. unfold vlan_split. rewrite HD. cbv zeta.
  assert (Hcn : cut_nul (skipn (S di) s) = skipn (S di) s).
  { apply cut_nul_id. intros K. apply HNN. exact (in_skipn _ _ _ K). }
  rewrite Hcn.
  replace ((16 <? di + 1)%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace ((16 <? strlen s + 1)%nat) with false
    by (symmetry; apply Nat.ltb_ge; rewrite strlen_id by exact HNN; lia).
  cbn [orb]. reflexivity.
Qed.

Lemma sc_unfold : forall di, strrchr s DOT = Some di -> (di < length s)%nat ->
  split_copy s =
    (if (di =? 0)%nat || (hd0 (skipn (S di) s) =? 0) then None else
     if negb (forallb isdigit (skipn (S di) s)) then None else
     if (strtol10 (skipn (S di) s) <? 1) || (4094 <? strtol10 (skipn (S di) s)) then None else
     Some di).
Proof.
  intros di HD Hdi. unfold split_copy. rewrite HD. cbv zeta.
  assert (Hcn : cut_nul (skipn (S di) s) = skipn (S di) s).
  { apply cut_nul_id. intros K. apply HNN. exact (in_skipn _ _ _ K). }
  rewrite Hcn.
  replace ((16 <? di + 1)%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace ((16 <? strlen s + 1)%nat) with false
    by (symmetry; apply Nat.ltb_ge; rewrite strlen_id by exact HNN; lia).
  cbn [orb]. reflexivity.
Qed.

Lemma tr_ec : forall m, munch [(Sp - 432, Sp)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (TP - 164) [C4 ev].
Proof.
  intros m MU WM. eapply rw_cells_transport; [exact HEC | exact MU | exact WM |].
  cbn [cells_size csize]. apply apt_dis1. eapply apt_sub; [exact HecA | lia | lia | lia].
Qed.

Lemma tr_got : forall m, munch [(Sp - 432, Sp)] m0 m ->
  bytes_at rsegs m (sa_got_guard SA) (le8 (Z_to_bv 64 (sa_guard SA))).
Proof.
  intros m MU. eapply bytes_at_transport; [exact HGOT | exact MU |].
  rewrite length_le8. cbn [disjoint_from]. pose proof got_lo. split; [lia | exact I].
Qed.

Lemma tr_grd : forall m, munch [(Sp - 432, Sp)] m0 m -> exists g : word, bytes_at rsegs m (sa_guard SA) (le8 g).
Proof.
  intros m MU. destruct HGRD as [g Hg]. exists g.
  eapply bytes_at_transport; [exact Hg | exact MU |].
  rewrite length_le8. cbn [disjoint_from]. pose proof grd_lo. split; [lia | exact I].
Qed.

(** ** The answer and the post *)

Local Abbreviation RV := (match vlan_split s with Some _ => 1 | None => 0 end).

Local Abbreviation Post := (fun ms' : machine_state =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 RV)
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch (split_W Sp TP parent vid s) m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo Sp /\
    rw_cells rsegs m' (TP - 164) [C4 ev] /\
    (match vlan_split s with
     | Some (p, v) => cstrz_at rsegs m' parent p /\ bytes_at rsegs m' vid (le2 (Z_to_bv 64 v))
     | None => True
     end)).

(** The exit 0x163f8: restore ra and s0-s5, free the frame, return with a0 = r. *)
Lemma epi : forall (r : Z) (m : word -> option byte)
    (x1 y0 y1 y2 w8 w9 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 w21 u3 u4 u5 u6 : word),
  r = RV ->
  (exists j0, rw_cells rsegs m (Sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
  stk rsegs m lo (Sp + -64) ->
  munch (split_W Sp TP parent vid s) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m (TP - 164) [C4 ev] ->
  (match vlan_split s with
   | Some (p, v) => cstrz_at rsegs m parent p /\ bytes_at rsegs m vid (le2 (Z_to_bv 64 v))
   | None => True
   end) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -64)) gp tp y0 y1 y2 w8 w9 (Z_to_bv 64 r) z1 z2 z3 z4 z5 z6 z7
             w18 w19 w20 w21 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x163f8) fc None m (seg_rom rsegs)).
Proof.
  intros r m x1 y0 y1 y2 w8 w9 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 w21 u3 u4 u5 u6 Er (j0 & FR) ST MU WM MI QE QV.
  do 9 step.
  apply evt_done.
  exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, u3, u4, u5, u6, m.
  split; [subst r; first [reflexivity | unfold mkR; repeat f_equal; lia]|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [| split; [exact QE | exact QV]].
  pose proof (stk_release rsegs m lo (Sp + -64) _ ST FR ltac:(lia)) as R.
  cbn [cells_size csize Nat.add] in R.
  replace (Sp + -64 + Z.of_nat 64) with Sp in R by lia. exact R.
Qed.

(** The digit loop 0x163b8 .. 0x163cc, on the bytes left before the NUL: it falls out at 0x163d0 with a4 = 0
    when every byte of [b :: l] is a digit, and jumps to 0x163f4 at the first byte that is not. The
    pointer-overflow trap at 0x163c0 is dead: p addresses a byte of the string, which bytes_at keeps below
    2^64 - 1. *)
Lemma dloop : forall (l : list byte) (b : byte) (q : Z) (m : word -> option byte) (Q : machine_state -> Prop)
    (A0 sp' : Z)
    (x1 y0 y1 y2 w8 w9 va1 va2 va3 va4 w15 w16 w17 w18 w19 w20 w21 u3 u4 u5 u6 : word),
  va1 = Z_to_bv 64 9 -> va2 = Z_to_bv 64 (-1) -> va3 = Z_to_bv 64 (segment + q) ->
  va4 = Z_to_bv 64 (bv_unsigned b) ->
  bytes_at rsegs m (segment + q) ((b :: l) ++ [ZERO]) ->
  ~ In ZERO (b :: l) ->
  (forallb isdigit (zs (b :: l)) = true ->
    forall z3 : word,
      evt rsegs Q (MS (mkR x1 (Z_to_bv 64 sp') gp tp y0 y1 y2 w8 w9 (Z_to_bv 64 A0) va1 va2 z3
                           (Z_to_bv 64 0) w15 w16 w17 w18 w19 w20 w21 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                      F (Z_to_bv 64 0x163d0) fc None m (seg_rom rsegs))) ->
  (forallb isdigit (zs (b :: l)) = false ->
    forall z3 z4 : word,
      evt rsegs Q (MS (mkR x1 (Z_to_bv 64 sp') gp tp y0 y1 y2 w8 w9 (Z_to_bv 64 A0) va1 va2 z3 z4
                           w15 w16 w17 w18 w19 w20 w21 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                      F (Z_to_bv 64 0x163f4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 sp') gp tp y0 y1 y2 w8 w9 (Z_to_bv 64 A0) va1 va2 va3 va4
                       w15 w16 w17 w18 w19 w20 w21 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 0x163b8) fc None m (seg_rom rsegs)).
Proof.
  intros l. induction l as [|c l IH];
    intros b q m Q A0 sp' x1 y0 y1 y2 w8 w9 va1 va2 va3 va4 w15 w16 w17 w18 w19 w20 w21 u3 u4 u5 u6
      Ea1 Ea2 Ea3 Ea4 HB HN HOK HNO; subst va1 va2 va3 va4.
  - (* the last byte before the NUL *)
    pose proof (sq_byte_range b) as RB.
    pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
    step. step.
    if_cases B; zify_cond B.
    + (* not a digit *)
      pose proof (dig_no (bv_unsigned b) RB B) as DB.
      apply HNO. cbn [zs map forallb]. rewrite DB. reflexivity.
    + pose proof (dig_yes (bv_unsigned b) RB ltac:(lia)) as DB.
      assert (RD : ov_read_bytes rsegs m (wa (segment + q + 1)) 1 = Some [ZERO]).
      { rewrite (bytes_at_read rsegs m (segment + q) ([b] ++ [ZERO]) 1 1 HB ltac:(lia) ltac:(cbn; lia)).
        reflexivity. }
      step. rewrite eqb_m1 by lia. cbv iota.
      step. step.
      rewrite zxb_zero.
      step. if_false.
      apply HOK. cbn [zs map forallb]. rewrite DB. reflexivity.
  - (* at least one byte after this one *)
    pose proof (sq_byte_range b) as RB. pose proof (sq_byte_range c) as RC.
    pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
    assert (HcZ : c <> ZERO) by (intros ->; apply HN; right; left; reflexivity).
    step. step.
    if_cases B; zify_cond B.
    + pose proof (dig_no (bv_unsigned b) RB B) as DB.
      apply HNO. cbn [zs map forallb]. rewrite DB. reflexivity.
    + pose proof (dig_yes (bv_unsigned b) RB ltac:(lia)) as DB.
      assert (RD : ov_read_bytes rsegs m (wa (segment + q + 1)) 1 = Some [c]).
      { rewrite (bytes_at_read rsegs m (segment + q) ((b :: c :: l) ++ [ZERO]) 1 1 HB ltac:(lia)
                   ltac:(rewrite length_app; cbn [length]; lia)).
        reflexivity. }
      step. rewrite eqb_m1 by lia. cbv iota.
      step. step.
      cbv delta [zxb].
      step.
      rewrite sq_eqb_lit by lia.
      replace (bv_unsigned c =? 0) with false by (symmetry; apply Z.eqb_neq; apply byte_nz; exact HcZ).
      cbn [negb]. cbv iota.
      eapply (IH c (q + 1) m Q A0 sp').
      * reflexivity.
      * reflexivity.
      * f_equal. lia.
      * reflexivity.
      * replace (segment + (q + 1)) with (segment + q + Z.of_nat (length [b])) by (cbn [length]; lia).
        apply (bat_suf rsegs m (segment + q) [b] ((c :: l) ++ [ZERO])).
        exact HB.
      * intros Hin. apply HN. right. exact Hin.
      * intros HD z3. apply HOK. cbn [zs map forallb] in HD |- *. rewrite DB. cbn [andb]. exact HD.
      * intros HD z3 z4. apply HNO. cbn [zs map forallb] in HD |- *. rewrite DB. cbn [andb]. exact HD.
Qed.

(** Weakening a callee's footprint to one of this walk's. *)
Ltac mush H :=
  eapply munch_weaken; [| exact H];
  unfold sub_fp; cbn [outside]; intros ?x Hx; repeat split; try exact I; lia.

(** The whole function from its entry 0x16338. *)
Lemma body : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 segment) (Z_to_bv 64 parent)
             (Z_to_bv 64 16) (Z_to_bv 64 vid) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16338) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6.
  pose proof epi as EP. pose proof dloop as DL.
  pose proof tr_seg as TRS. pose proof tr_seg2 as TRS2. pose proof tr_par as TRP.
  pose proof tr_par2 as TRP2. pose proof tr_vid as TRV. pose proof tr_ec as TRE.
  pose proof tr_got as TRG. pose proof tr_grd as TRD.
  pose proof got_lo as GL. pose proof grd_lo as GDL. pose proof ec_guard as ECG.
  pose proof seg_b as SB. pose proof par_b as PB2. pose proof vid_b as VB.
  pose proof (munch_refl [(Sp - 432, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 64 HST ltac:(lia)) as [ST1 [junk FR]].
  change (Z.of_nat 64) with 64 in ST1, FR.
  replace (Sp - 64) with (Sp + -64) in ST1, FR by lia.
  do 8 step.
  lazymatch type of FR with
  | rw_cells _ _ _ (CB 8 ?j :: _) => remember j as j0 eqn:Ej0; clear Ej0
  end.
  (* s2 = segment; a0 = 0; the four `beqz` *)
  step. step. step.
  rewrite sq_eqb_lit by lia.
  replace (segment =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step.
  rewrite sq_eqb_lit by lia.
  replace (parent =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step. if_false.
  step. step.
  rewrite sq_eqb_lit by lia.
  replace (vid =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  (* a1 = '.'; a0 = segment; jal strrchr *)
  step. step. step.
  (* strrchr(segment, '.') at 0x1ef60 *)
  eapply evt_cut.
  { eapply HSRCH with (str := bs) (slack := sl) (lo := lo); rewrite ?unsigned_lit by lia.
    - apply TRS. exact MU.
    - exact HNZ.
    - exact HSK.
    - assumption.
    - exact ST1.
    - unfold STRRCHR_K. lia.
    - unfold STRRCHR_K. pose proof (apt_or _ _ _ _ HsegA) as K. lia. }
  intros ms' (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 &
              -> & MU1 & WM1 & MI1 & ST2 & HB1).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (unsigned_lit segment) in HB1 by lia.
  rewrite (unsigned_lit (Sp + -64)) in MU1, ST2 by lia.
  unfold STRRCHR_K in MU1.
  rewrite (unsigned_lit segment), (unsigned_lit 46) by lia.
  change (46 mod 256) with 46.
  rewrite (SegBridge.bridge_strrchr segment 46 bs HNZ ltac:(lia)), HZB.
  assert (MU2 : munch [(Sp - 432, Sp)] m0 m1) by (eapply munch_trans; [exact MU | mush MU1]).
  assert (WM2 : wmono rsegs m0 m1) by (eapply wmono_trans; [exact WM | exact WM1]).
  assert (FR1 : rw_cells rsegs m1 (Sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 |
      cbn [cells_size csize Nat.add disjoint_from]; split; [lia | exact I]]. }
  clear FR MU MU1 WM WM1 ST1.
  destruct (strrchr s DOT) as [di|] eqn:HD.
  2:{ (* no '.': strrchr answered NULL, the function returns 0 *)
    assert (HVS : vlan_split s = None) by (unfold vlan_split; rewrite HD; reflexivity).
    assert (HSC : split_copy s = None) by (unfold split_copy; rewrite HD; reflexivity).
    step. step. step.
    rewrite sq_eqb_lit by lia. rewrite Z.eqb_refl. cbv iota.
    eapply EP.
    - rewrite HVS. reflexivity.
    - eexists. exact FR1.
    - exact ST2.
    - apply mw_none; [exact HSC | exact HVS | exact MU2].
    - exact WM2.
    - exact MI1.
    - apply TRE; [exact MU2 | exact WM2].
    - rewrite HVS. exact I. }
  (* a '.' at index di *)
  assert (Hdi : (di < length s)%nat).
  { pose proof (strrchr_lt s DOT di HD) as K. rewrite (cut_nul_id s HNN) in K. exact K. }
  pose proof (vs_unfold di HD Hdi) as VU. pose proof (sc_unfold di HD Hdi) as SU.
  assert (Hdib : 0 <= segment + Z.of_nat di < 2 ^ 64) by lia.
  step. step. step.
  rewrite sq_eqb_lit by lia.
  replace (segment + Z.of_nat di =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step.
  rewrite sq_eqb_lit by lia.
  destruct (Nat.eq_dec di 0) as [Hd0|Hd0].
  { (* dot at the start: 0 *)
    subst di.
    assert (HVS : vlan_split s = None) by (rewrite VU; reflexivity).
    assert (HSC : split_copy s = None) by (rewrite SU; reflexivity).
    replace (segment + Z.of_nat 0 =? segment) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
    eapply EP.
    - rewrite HVS. reflexivity.
    - eexists. exact FR1.
    - exact ST2.
    - apply mw_none; [exact HSC | exact HVS | exact MU2].
    - exact WM2.
    - exact MI1.
    - apply TRE; [exact MU2 | exact WM2].
    - rewrite HVS. exact I. }
  replace (segment + Z.of_nat di =? segment) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  (* 0x1639c: dot = 2^64 - 1 is refuted by the segment's extent; then a0 = dot + 1 *)
  step. step.
  rewrite eqb_m1 by lia. cbv iota.
  step.
  (* dot[1]: the byte at segment + di + 1 *)
  assert (HBS : bytes_at rsegs m1 (segment + Z.of_nat (S di)) (skipn (S di) bs ++ ZERO :: sl)).
  { replace (segment + Z.of_nat (S di)) with (segment + Z.of_nat (length (firstn (S di) bs)))
      by (rewrite length_firstn, Nat.min_l by lia; reflexivity).
    apply (bat_suf rsegs m1 segment (firstn (S di) bs) (skipn (S di) bs ++ ZERO :: sl)).
    rewrite app_assoc, firstn_skipn. exact HB1. }
  assert (Hsk : skipn (S di) s = zs (skipn (S di) bs)) by (rewrite zs_skipn, HZB; reflexivity).
  destruct (skipn (S di) bs) as [|b tl] eqn:Etl.
  - (* the dot is the last byte: dot[1] is the NUL, 0 *)
    cbn [app] in HBS. cbn [zs map] in Hsk.
    assert (HVS : vlan_split s = None).
    { rewrite VU, Hsk. destruct ((di =? 0)%nat); reflexivity. }
    assert (HSC : split_copy s = None).
    { rewrite SU, Hsk. destruct ((di =? 0)%nat); reflexivity. }
    assert (RD0 : ov_read_bytes rsegs m1 (wa (segment + Z.of_nat di + 1)) 1 = Some [ZERO]).
    { replace (segment + Z.of_nat di + 1) with (segment + Z.of_nat (S di) + 0) by lia.
      rewrite (bytes_at_read rsegs m1 (segment + Z.of_nat (S di)) (ZERO :: sl) 0 1 HBS
                 ltac:(lia) ltac:(cbn [length]; lia)).
      reflexivity. }
    step.
    rewrite zxb_zero.
    step. if_true.
    step.
    eapply EP.
    + rewrite HVS. reflexivity.
    + eexists. exact FR1.
    + exact ST2.
    + apply mw_none; [exact HSC | exact HVS | exact MU2].
    + exact WM2.
    + exact MI1.
    + apply TRE; [exact MU2 | exact WM2].
    + rewrite HVS. exact I.
  - (* at least one byte after the dot: the digit loop *)
    assert (HbZ : b <> ZERO).
    { intros ->. apply HNZ. apply (in_skipn (S di) bs ZERO). rewrite Etl. left. reflexivity. }
    assert (RD0 : ov_read_bytes rsegs m1 (wa (segment + Z.of_nat di + 1)) 1 = Some [b]).
    { replace (segment + Z.of_nat di + 1) with (segment + Z.of_nat (S di) + 0) by lia.
      rewrite (bytes_at_read rsegs m1 (segment + Z.of_nat (S di)) ((b :: tl) ++ ZERO :: sl) 0 1 HBS
                 ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia)).
      reflexivity. }
    pose proof (sq_byte_range b) as RBb.
    step.
    cbv delta [zxb].
    step.
    rewrite sq_eqb_lit by lia.
    replace (bv_unsigned b =? 0) with false by (symmetry; apply Z.eqb_neq; apply byte_nz; exact HbZ).
    cbv iota.
    step. step. step.
    eapply (DL tl b (Z.of_nat di + 1) m1 Post (segment + Z.of_nat di + 1) (Sp + -64)).
    + reflexivity.
    + reflexivity.
    + f_equal. lia.
    + reflexivity.
    + replace (segment + (Z.of_nat di + 1)) with (segment + Z.of_nat (S di)) by lia.
      apply (bat_pre rsegs m1 (segment + Z.of_nat (S di)) ((b :: tl) ++ [ZERO]) sl).
      rewrite <- app_assoc. exact HBS.
    + intros K. apply HNZ. apply (in_skipn (S di) bs ZERO). rewrite Etl. exact K.
    + (* every byte of the tail is a digit: strtol(dot + 1, NULL, 10) *)
      intros HDIG z3.
      assert (Hlt : length bs = (S di + S (length tl))%nat).
      { pose proof (length_skipn (S di) bs) as K. rewrite Etl in K. cbn [length] in K. lia. }
      assert (HBT : bytes_at rsegs m1 (segment + Z.of_nat di + 1) ((b :: tl) ++ [ZERO])).
      { replace (segment + Z.of_nat di + 1) with (segment + Z.of_nat (S di)) by lia.
        apply (bat_pre rsegs m1 (segment + Z.of_nat (S di)) ((b :: tl) ++ [ZERO]) sl).
        rewrite <- app_assoc. exact HBS. }
      destruct (TRD m1 MU2) as [g Hg].
      pose proof (TRE m1 MU2 WM2) as HEC1.
      step. step. step.
      eapply evt_cut.
      { eapply HSTOL with (A := segment + Z.of_nat di + 1) (str := b :: tl) (ev := ev) (can := g) (lo := lo);
          rewrite ?unsigned_lit, ?Etp by lia.
        - exact HBT.
        - cbn [length]. lia.
        - replace (TP + -164) with (TP - 164) by lia. exact HEC1.
        - exact (TRG m1 MU2).
        - exact Hg.
        - exact ST2.
        - lia.
        - pose proof (apt_or _ _ _ _ HsegA) as K. cbn [length]. lia.
        - pose proof (apt_or _ _ _ _ HecA) as K. lia.
        - left. exact GL.
        - left. exact GDL.
        - lia.
        - assumption. }
      intros ms' (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & m2 &
                  -> & MU3 & WM3 & MI3 & ST3 & HEC2).
      rewrite ret_pc_even by (try lia; reflexivity).
      rewrite (unsigned_lit (Sp + -64)) in MU3, ST3 by lia.
      rewrite Etp in MU3, HEC2.
      replace (TP + -164) with (TP - 164) in MU3, HEC2 by lia.
      rewrite (SegBridge.bridge_strtol10_errno (b :: tl) ev ltac:(discriminate) HDIG
                 ltac:(cbn [length]; lia)) in HEC2.
      rewrite (SegBridge.bridge_strtol10_str (b :: tl) ltac:(discriminate) HDIG
                 ltac:(cbn [length]; lia)).
      pose proof (SegBridge.strtol10_bound (b :: tl) HDIG ltac:(cbn [length]; lia)) as HVB.
      assert (MU4 : munch [(Sp - 432, Sp); (TP - 164, TP - 164 + 4)] m0 m2)
        by (eapply munch_trans; [mush MU2 | mush MU3]).
      assert (WM4 : wmono rsegs m0 m2) by (eapply wmono_trans; [exact WM2 | exact WM3]).
      assert (FR2 : rw_cells rsegs m2 (Sp + -64)
                      [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_transport; [exact FR1 | exact MU3 | exact WM3 |].
        pose proof (apt_or _ _ _ _ HecA) as K.
        cbn [cells_size csize Nat.add disjoint_from]. repeat split; try exact I; lia. }
      (* the model, with the two tests before the digits settled *)
      rewrite Hsk in VU, SU. rewrite HDIG in VU, SU. cbn [negb] in VU, SU.
      replace ((di =? 0)%nat) with false in VU, SU by (symmetry; apply Nat.eqb_neq; exact Hd0).
      replace (hd0 (zs (b :: tl)) =? 0) with false in VU, SU
        by (symmetry; apply Z.eqb_neq; cbn [zs map hd0]; apply byte_nz; exact HbZ).
      cbn [orb] in VU, SU.
      clear MU2 MU3 WM2 WM3 FR1 HEC1 HB1 HBS HBT Hg.
      step. step. step. step. step. step.
      if_cases B; zify_cond B.
      * (* 1 <= v <= 4094 *)
        pose proof (rng_in (strtol10 (zs (b :: tl))) ltac:(lia) B) as HRG0.
        assert (HRG : ((strtol10 (zs (b :: tl)) <? 1) || (4094 <? strtol10 (zs (b :: tl))))%bool = false)
          by (apply orb_false_iff; split; apply Z.ltb_ge; lia).
        rewrite HRG in VU, SU. cbv iota in VU, SU.
        (* plen = dot - segment *)
        step.
        rewrite (unsigned_lit (segment + Z.of_nat di)), (unsigned_lit segment) by lia.
        replace (segment + Z.of_nat di - segment) with (Z.of_nat di) by lia.
        step. step. step.
        rewrite bv_ltu_Z, (unsigned_lit 16), (unsigned_lit (Z.of_nat di + 1)) by lia.
        replace (16 <? Z.of_nat di + 1) with false by (symmetry; apply Z.ltb_ge; lia).
        cbv iota.
        step. step.
        rewrite bv_ltu_Z, (unsigned_lit 16), (unsigned_lit (Z.of_nat di + 1)) by lia.
        replace (16 <? Z.of_nat di + 1) with false by (symmetry; apply Z.ltb_ge; lia).
        cbv iota.
        (* strlen(segment) *)
        step. step.
        eapply evt_cut.
        { eapply HSLEN with (str := bs) (slack := sl); rewrite ?unsigned_lit by lia.
          - apply TRS2. exact MU4.
          - exact HNZ.
          - exact HSK.
          - exact MI3. }
        intros ms' (d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & d8 & d9 & d10 & d11 & d12 & d13 & m3 &
                    -> & MU5 & WM5 & MI5 & HB3).
        rewrite ret_pc_even by (try lia; reflexivity).
        rewrite (unsigned_lit segment) in HB3 by lia.
        assert (MU6 : munch [(Sp - 432, Sp); (TP - 164, TP - 164 + 4)] m0 m3)
          by (eapply munch_trans; [exact MU4 | mush MU5]).
        assert (WM6 : wmono rsegs m0 m3) by (eapply wmono_trans; [exact WM4 | exact WM5]).
        assert (FR3 : rw_cells rsegs m3 (Sp + -64)
                        [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply rw_cells_transport; [exact FR2 | exact MU5 | exact WM5 | exact I]. }
        assert (HEC3 : rw_cells rsegs m3 (TP - 164) [C4 ev])
          by (eapply tr_ec_mv; [exact HEC2 | exact MU5 | exact WM5 | exact I]).
        assert (ST4 : stk rsegs m3 lo (Sp + -64))
          by (eapply stk_transport_disjoint; [exact ST3 | exact MU5 | exact WM5 | exact I]).
        clear MU5 WM5 FR2 HEC2 ST3 MU4 WM4.
        (* strlen(segment) < 16 *)
        step. step. step.
        rewrite bv_ltu_Z, (unsigned_lit_wrap (Z.of_nat (length bs) + -16)), (unsigned_lit_wrap (-17)).
        rewrite (len_test (Z.of_nat (length bs)) ltac:(lia)). cbv iota.
        (* memcpy(parent, segment, plen) *)
        assert (HSRC : bytes_at rsegs m3 segment (firstn di bs)).
        { apply (bat_pre rsegs m3 segment (firstn di bs) (skipn di bs ++ ZERO :: sl)).
          rewrite app_assoc, firstn_skipn. exact HB3. }
        destruct (rw_cb_split rsegs m3 parent 16 di pb (TRP2 m3 MU6 WM6) ltac:(lia)) as [HPA HPT].
        step. step. step. step.
        eapply evt_cut.
        { eapply HMCPY with (src := firstn di bs) (junk := firstn di pb);
            rewrite ?unsigned_lit by lia.
          - exact HSRC.
          - rewrite length_firstn, Nat2Z.id. lia.
          - rewrite Nat2Z.id. exact HPA.
          - pose proof (apt_or _ _ _ _ HsegP) as K. lia.
          - exact MI5. }
        intros ms' (e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & e12 & e13 & m4 &
                    -> & MU7 & WM7 & MI7 & HPC & HSRC4).
        rewrite ret_pc_even by (try lia; reflexivity).
        rewrite (unsigned_lit parent), (unsigned_lit (Z.of_nat di)), Nat2Z.id in HPC by lia.
        rewrite (unsigned_lit segment) in HSRC4 by lia.
        rewrite (unsigned_lit parent), (unsigned_lit (Z.of_nat di)) in MU7 by lia.
        assert (HPT4 : rw_cells rsegs m4 (parent + Z.of_nat di) [CB (16 - di) (skipn di pb)]).
        { eapply rw_cells_transport; [exact HPT | exact MU7 | exact WM7 |].
          cbn [cells_size csize Nat.add disjoint_from]. split; [lia | exact I]. }
        assert (FR4 : rw_cells rsegs m4 (Sp + -64)
                        [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply rw_cells_transport; [exact FR3 | exact MU7 | exact WM7 |].
          pose proof (apt_or _ _ _ _ HparA) as K.
          cbn [cells_size csize Nat.add disjoint_from]. split; [lia | exact I]. }
        assert (HEC4 : rw_cells rsegs m4 (TP - 164) [C4 ev]).
        { eapply tr_ec_mv; [exact HEC3 | exact MU7 | exact WM7 |].
          pose proof (apt_or _ _ _ _ HecP) as K. cbn [disjoint_from]. split; [lia | exact I]. }
        assert (ST5 : stk rsegs m4 lo (Sp + -64)).
        { eapply stk_transport_disjoint; [exact ST4 | exact MU7 | exact WM7 |].
          pose proof (apt_or _ _ _ _ HparA) as K. cbn [disjoint_from]. split; [lia | exact I]. }
        (* 0x1645c: parent + plen does not wrap; then s4 = parent + plen *)
        step. step.
        rewrite bv_ltu_Z, (not_val parent), (unsigned_lit (Z.of_nat di)) by lia.
        replace (18446744073709551615 - parent <? Z.of_nat di) with false
          by (symmetry; apply Z.ltb_ge; lia).
        cbv iota.
        (* parent[plen] = 0 *)
        step.
        assert (SOK : store_ok rsegs m4 (wa (parent + Z.of_nat di + 0)) 1 = true).
        { pose proof HPT4 as HW. destruct HW as [_ W]. cbn [cells_size csize] in W.
          apply (wr_at_store_ok rsegs m4 (parent + Z.of_nat di) (Z.of_nat (16 - di + 0)) 0 1 W); lia. }
        rewrite Z.add_0_r in SOK.
        assert (MU8 : munch [(Sp - 432, Sp); (TP - 164, TP - 164 + 4);
                             (parent, parent + Z.of_nat di + 1)] m0 m4)
          by (eapply munch_trans; [mush MU6 | mush MU7]).
        assert (WM8 : wmono rsegs m0 m4) by (eapply wmono_trans; [exact WM6 | exact WM7]).
        pose proof HPC as HPCb. destruct HPCb as [[_ HB4] _].
        cbn [cells_bytes cbytes] in HB4. rewrite app_nil_r in HB4.
        assert (Lfb : length (firstn di bs) = di) by (rewrite length_firstn; lia).
        step.
        rewrite le1_zero.
        remember (write_to_mem m4 (Z_to_bv 64 (parent + Z.of_nat di)) [ZERO]) as m5 eqn:Em5.
        assert (HPAR5 : bytes_at rsegs m5 parent (firstn di bs ++ [ZERO])).
        { rewrite Em5. apply bytes_at_app. split.
          - apply bytes_at_write_other; [exact HB4 | lia | cbn [length]; lia | lia].
          - rewrite Lfb. apply bytes_at_write_same; [lia | cbn [length]; lia]. }
        assert (HEC5 : rw_cells rsegs m5 (TP - 164) [C4 ev]).
        { rewrite Em5. pose proof (apt_or _ _ _ _ HecP) as K.
          apply rw_cells_frame; [exact HEC4 | lia | cbn [length]; lia |].
          cbn [cells_size csize length Nat.add]. lia. }
        assert (FR5 : rw_cells rsegs m5 (Sp + -64)
                        [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { rewrite Em5. pose proof (apt_or _ _ _ _ HparA) as K.
          apply rw_cells_frame; [exact FR4 | lia | cbn [length]; lia |].
          cbn [cells_size csize length Nat.add]. lia. }
        assert (ST6 : stk rsegs m5 lo (Sp + -64)).
        { rewrite Em5. apply stk_write; [exact ST5 | lia | cbn [length]; lia]. }
        assert (MU9 : munch [(Sp - 432, Sp); (TP - 164, TP - 164 + 4);
                             (parent, parent + Z.of_nat di + 1)] m0 m5).
        { rewrite Em5. apply munch_write; [exact MU8 | lia | cbn [length]; lia |].
          cbn [inside length]. lia. }
        assert (WM9 : wmono rsegs m0 m5) by (rewrite Em5; apply wmono_write; exact WM8).
        assert (MI9 : mem_inv rsegs m5).
        { rewrite Em5. apply mem_inv_store; [exact MI7 | cbn [length]; exact SOK]. }
        clear MU6 MU7 WM6 WM7 FR3 FR4 HEC3 HEC4 ST4 ST5 HPT HPT4 HB3 HB4 HSRC HSRC4 HPA HPC.
        assert (Lfs : length (firstn di s) = di) by (rewrite length_firstn; lia).
        assert (HZF : zs (firstn di bs) = firstn di s) by (rewrite zs_firstn, HZB; reflexivity).
        assert (HNF : ~ In 0 (firstn di s)) by (intros K; apply HNN; exact (in_firstn _ _ _ K)).
        (* name_ok(parent) *)
        step. step.
        eapply evt_cut.
        { eapply HNOK with (lo := lo) (nm := firstn di s).
          unfold name_ok_pre. rewrite (unsigned_lit parent), (unsigned_lit (Sp + -64)) by lia.
          split; [lia|]. split.
          - unfold cstrz_at. exists (firstn di bs). split; [exact HPAR5 | split; [exact HZF | exact HNF]].
          - split.
            + rewrite Lfs. eapply apt_sub; [exact HparA | lia | lia | lia].
            + split; [| exact MI9].
              unfold stack_ok, NAME_OK_STACK. split; [exact ST6|]. split; [lia|]. split.
              * replace (Sp + -64) with (Sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact HSp16.
              * intros a Ha. apply HROM. lia. }
        intros ms' (f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & f9 & f10 & f11 & f12 & f13 & m6 &
                    -> & MU10 & WM10 & MI10 & ST7 & _).
        rewrite ret_pc_even by (try lia; reflexivity).
        rewrite (unsigned_lit (Sp + -64)) in MU10, ST7 by lia.
        unfold NAME_OK_STACK in MU10.
        assert (HPAR6 : bytes_at rsegs m6 parent (firstn di bs ++ [ZERO])).
        { eapply bytes_at_transport; [exact HPAR5 | exact MU10 |].
          pose proof (apt_or _ _ _ _ HparA) as K.
          rewrite length_app, Lfb. cbn [length disjoint_from]. split; [lia | exact I]. }
        assert (HEC6 : rw_cells rsegs m6 (TP - 164) [C4 ev]).
        { eapply tr_ec_mv; [exact HEC5 | exact MU10 | exact WM10 |].
          pose proof (apt_or _ _ _ _ HecA) as K. cbn [disjoint_from]. split; [lia | exact I]. }
        assert (FR6 : rw_cells rsegs m6 (Sp + -64)
                        [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply rw_cells_transport; [exact FR5 | exact MU10 | exact WM10 |].
          cbn [cells_size csize Nat.add disjoint_from]. split; [lia | exact I]. }
        assert (MU11 : munch [(Sp - 432, Sp); (TP - 164, TP - 164 + 4);
                              (parent, parent + Z.of_nat di + 1)] m0 m6)
          by (eapply munch_trans; [exact MU9 | mush MU10]).
        assert (WM11 : wmono rsegs m0 m6) by (eapply wmono_trans; [exact WM9 | exact WM10]).
        assert (WV6 : wr_at rsegs m6 vid 2) by (apply TRV; exact WM11).
        destruct (name_ok (firstn di s)) eqn:HNOv; cbn [b2z].
        -- (* name_ok: *vid = v, return 1 *)
           assert (HVS : vlan_split s = Some (firstn di s, strtol10 (zs (b :: tl)) mod 65536))
             by (rewrite VU; reflexivity).
           step.
           rewrite sq_eqb_lit by lia. replace (1 =? 0) with false by reflexivity. cbv iota.
           (* 0x16478: vid & 1 = 0 *)
           step.
           rewrite (unsigned_lit vid), (land1 vid), Hvid2 by lia.
           step. if_false.
           assert (SOK2 : store_ok rsegs m6 (wa (vid + 0)) 2 = true)
             by (apply (wr_at_store_ok rsegs m6 vid 2 0 2 WV6); lia).
           rewrite Z.add_0_r in SOK2.
           step.
           remember (write_to_mem m6 (Z_to_bv 64 vid) (le2 (Z_to_bv 64 (strtol10 (zs (b :: tl))))))
             as m7 eqn:Em7.
           assert (HVID7 : bytes_at rsegs m7 vid (le2 (Z_to_bv 64 (strtol10 (zs (b :: tl)))))).
           { rewrite Em7. apply bytes_at_write_same; [lia | rewrite length_le2; lia]. }
           assert (HPAR7 : bytes_at rsegs m7 parent (firstn di bs ++ [ZERO])).
           { rewrite Em7. pose proof (apt_or _ _ _ _ HvidP) as K.
             apply bytes_at_write_other; [exact HPAR6 | lia | rewrite length_le2; lia |].
             rewrite length_app, Lfb, length_le2. cbn [length]. lia. }
           assert (HEC7 : rw_cells rsegs m7 (TP - 164) [C4 ev]).
           { rewrite Em7. pose proof (apt_or _ _ _ _ HecV) as K.
             apply rw_cells_frame; [exact HEC6 | lia | rewrite length_le2; lia |].
             cbn [cells_size csize]. rewrite length_le2. lia. }
           assert (FR7 : rw_cells rsegs m7 (Sp + -64)
                           [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
           { rewrite Em7. pose proof (apt_or _ _ _ _ HvidA) as K.
             apply rw_cells_frame; [exact FR6 | lia | rewrite length_le2; lia |].
             cbn [cells_size csize Nat.add]. rewrite length_le2. lia. }
           assert (ST8 : stk rsegs m7 lo (Sp + -64)).
           { rewrite Em7. apply stk_write; [exact ST7 | lia | rewrite length_le2; lia]. }
           assert (MU12 : munch [(Sp - 432, Sp); (TP - 164, TP - 164 + 4);
                                 (parent, parent + Z.of_nat di + 1); (vid, vid + 2)] m0 m7).
           { rewrite Em7. apply munch_write; [mush MU11 | lia | rewrite length_le2; lia |].
             cbn [inside]. rewrite length_le2. lia. }
           assert (WM12 : wmono rsegs m0 m7) by (rewrite Em7; apply wmono_write; exact WM11).
           assert (MI12 : mem_inv rsegs m7).
           { rewrite Em7. apply mem_inv_store; [exact MI10 | rewrite length_le2; exact SOK2]. }
           step. step.
           eapply EP.
           ++ rewrite HVS. reflexivity.
           ++ eexists. exact FR7.
           ++ exact ST8.
           ++ eapply mw_full; [exact SU | exact HVS | exact MU12].
           ++ exact WM12.
           ++ exact MI12.
           ++ exact HEC7.
           ++ rewrite HVS. split.
              ** unfold cstrz_at. exists (firstn di bs).
                 split; [exact HPAR7 | split; [exact HZF | exact HNF]].
              ** rewrite (Z.mod_small (strtol10 (zs (b :: tl))) 65536) by lia. exact HVID7.
        -- (* not a name: 0 *)
           assert (HVS : vlan_split s = None) by (rewrite VU; reflexivity).
           step.
           rewrite sq_eqb_lit by lia. rewrite Z.eqb_refl. cbv iota.
           eapply EP.
           ++ rewrite HVS. reflexivity.
           ++ eexists. exact FR6.
           ++ exact ST7.
           ++ eapply mw_copy; [exact SU | exact HVS | exact MU11].
           ++ exact WM11.
           ++ exact MI10.
           ++ exact HEC6.
           ++ rewrite HVS. exact I.
      * (* v outside [1, 4094]: 0 *)
        pose proof (rng_out (strtol10 (zs (b :: tl))) ltac:(lia) B) as HRG.
        assert (HVS : vlan_split s = None) by (rewrite VU, HRG; reflexivity).
        assert (HSC : split_copy s = None) by (rewrite SU, HRG; reflexivity).
        step.
        eapply EP.
        -- rewrite HVS. reflexivity.
        -- eexists. exact FR2.
        -- exact ST3.
        -- unfold split_W, SPLIT_STACK. rewrite HSC, HVS. cbn [app]. exact MU4.
        -- exact WM4.
        -- exact MI3.
        -- exact HEC2.
        -- rewrite HVS. exact I.
    + (* a byte that is not a digit: 0 *)
      intros HDIG z3 z4.
      assert (HVS : vlan_split s = None).
      { rewrite VU, Hsk, HDIG. destruct ((di =? 0)%nat || (hd0 (zs (b :: tl)) =? 0)); reflexivity. }
      assert (HSC : split_copy s = None).
      { rewrite SU, Hsk, HDIG. destruct ((di =? 0)%nat || (hd0 (zs (b :: tl)) =? 0)); reflexivity. }
      step.
      eapply EP.
      * rewrite HVS. reflexivity.
      * eexists. exact FR1.
      * exact ST2.
      * apply mw_none; [exact HSC | exact HVS | exact MU2].
      * exact WM2.
      * exact MI1.
      * apply TRE; [exact MU2 | exact WM2].
      * rewrite HVS. exact I.
Qed.

End Split.

Theorem reac_declared_vlan_split_holds :
  strrchr_contract -> strtol_null_contract -> strlen_contract -> memcpy_contract -> name_ok_contract ->
  reac_declared_vlan_split_contract.
Proof.
  intros HSRCH HSTOL HSLEN HMCPY HNOK.
  unfold reac_declared_vlan_split_contract, split_pre, errno_ok, ssp_ok, stack_ok, SPLIT_STACK,
    REAC_DECLARED_VLAN_SPLIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo s ev
    (Hs0 & HCS & Hlen & Hsegb & HsegA & Hp0 & Hcap & (pb & HPB) & HparA & HsegP &
     Hv0 & Hvid2 & HWV & HvidA & HvidP & (HEC & HecA & HecG) & HecS & HecP & HecV &
     (HGOT & HGRD) & Himg & (HST & HKD & HSp16 & HROM) & HMI).
  destruct (cstr_cut rsegs m (bv_unsigned a0) s HCS) as (bs & sl & HB0 & HZB & HNN & HNZ & HLB & HSK & HSL8).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a3) as Ra3.
  pose proof (bv_unsigned_in_range 64 tp) as Rtp.
  change (bv_modulus 64) with (2 ^ 64) in Rsp, Ra0, Ra1, Ra3, Rtp.
  pose proof (proj1 HST) as Hlo0.
  pose proof (Z_to_bv_bv_unsigned sp) as Esp. pose proof (Z_to_bv_bv_unsigned a0) as Ea0.
  pose proof (Z_to_bv_bv_unsigned a1) as Ea1. pose proof (Z_to_bv_bv_unsigned a3) as Ea3.
  assert (Ea2 : Z_to_bv 64 16 = a2) by (rewrite <- Hcap; apply Z_to_bv_bv_unsigned).
  set (TP := bv_unsigned tp) in *.
  set (Sp := bv_unsigned sp) in *. set (segment := bv_unsigned a0) in *.
  set (parent := bv_unsigned a1) in *. set (vid := bv_unsigned a3) in *.
  rewrite <- Esp, <- Ea0, <- Ea1, <- Ea2, <- Ea3.
  assert (Etp : bv_unsigned tp = TP) by reflexivity.
  clearbody TP Sp segment parent vid. clear Esp Ea0 Ea1 Ea2 Ea3 Hcap HCS.
  eapply evt_mono.
  - eapply (body ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m Sp lo TP segment parent vid s ev
              bs sl pb); first [eassumption | lia].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MU & WM & MI & ST & QE & QV).
    unfold ret_post.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [rewrite unsigned_lit by lia; exact ST|].
    split; [exact QE | exact QV].
Qed.
