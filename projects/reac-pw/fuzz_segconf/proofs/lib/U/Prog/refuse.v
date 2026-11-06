From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Image Bytes ZBridge FP.
(* The plain walk's image-free lemmas (lists, bytes, printf text, encodings, transports). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import refuse.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env refuse_c refuse_pf_c.
Import ListNotations.
Open Scope Z_scope.

(** refuse (reac_segconf.c:30-48; UBSan image 1696d6c34ffd, 0x15c80, 77 instructions, U:706-791) against
    refuse_contract (U/Prog/refuse_c.v), with its two printf calls as premises (rf_snprintf and rf_vsnprintf,
    U/Prog/refuse_pf_c.v). The walk of Prog/refuse.v (its image-free lemmas are imported from there) with the
    UBSan code: every branch to the trap `unimp` at 0x15db0 is refuted from the premise: c & 7 (c mod 16 = 0),
    n_refusals >= 9 (here n <= 7), ~(c + 0x2e88) < 200 n and ~dst < k (the block lies inside the address space),
    n_refusals + 1 < n_refusals (n <= 7). *)

Lemma task_mem_munch : forall segs W m m', U.MemNorm.task_mem segs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd segs m x <> None) -> U.MemNorm.task_mem segs m'.
Proof.
  intros segs W m m' T MU P x b Hx.
  destruct (outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho) in Hx. exact (T x b Hx).
  - specialize (P x Ho). unfold mrd in P. destruct (m x) as [b0|] eqn:E.
    + exact (T x b0 E).
    + left. intros Hf. apply P. exact (U.MemNorm.seg_rom_unmapped segs x Hf).
Qed.

(** * The image (UBSan 1696d6c34ffd) *)
(** The reserved segments of the image, page-rounded: the four PT_LOADs. *)
Definition RES : list (Z * Z) := [(0x10000, 0x3000); (0x13000, 0xe000); (0x21000, 0x2000); (0x23000, 0x32000)].

Lemma res_eq : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs) = RES.
Proof. vm_compute. reflexivity. Qed.

Lemma segs_eq : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs = RES.
Proof. vm_compute. reflexivity. Qed.

Lemma noimg_res : forall c n, blk_noimg rsegs c n -> forall B Sz, In (B, Sz) RES ->
  forall i, 0 <= i < n -> ~ (B <= c + i < B + Sz).
Proof.
  intros c n H B Sz Hin i Hi. rewrite <- res_eq in Hin. apply in_map_iff in Hin as (s & Es & Hs).
  injection Es as E1 E2. specialize (H i Hi s Hs). rewrite E1, E2 in H. exact H.
Qed.

Lemma noimg_sub : forall c N a n, blk_noimg rsegs c N -> c <= a -> a + n <= c + N -> blk_noimg rsegs a n.
Proof.
  intros c N a n H H1 H2 i Hi s Hs. replace (a + i) with (c + (a - c + i)) by lia. apply H; [lia | exact Hs].
Qed.

(** A block covered by no reserved segment is apart from bytes of a reserved segment. *)
Lemma noimg_disj : forall c N B Sz p k q l, blk_noimg rsegs c N -> In (B, Sz) RES ->
  B <= p -> p + k <= B + Sz -> 0 < k -> c <= q -> q + l <= c + N -> 0 < l -> q + l <= p \/ p + k <= q.
Proof.
  intros c N B Sz p k q l H Hin H1 H2 Hk H3 H4 Hl.
  destruct (Z_le_dec (q + l) p) as [?|Hqp]; [left; lia|]. destruct (Z_le_dec (p + k) q) as [?|Hpq]; [right; lia|].
  exfalso. apply (noimg_res c N H B Sz Hin (Z.max p q - c)); lia.
Qed.

Lemma fs_some : forall (sl : list Segment) a n, 0 < n -> find_segment sl a n <> None ->
  exists sg, In sg sl /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  induction sl as [|sg rest IH]; intros a n Hn H; [cbn [find_segment] in H; contradiction|].
  revert H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base sg)) a) as [Hb1|Hb1]; cbn [andb];
    [destruct (Z.leb_spec (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) as [Hb2|Hb2]; cbn [andb] |]; intros H.
  - exists sg. split; [left; reflexivity | lia].
  - destruct (IH a n Hn H) as (s & Hs & Hr). exists s. split; [right; exact Hs | exact Hr].
  - destruct (IH a n Hn H) as (s & Hs & Hr). exists s. split; [right; exact Hs | exact Hr].
Qed.

Lemma res_none : forall x, (forall B Sz, In (B, Sz) RES -> ~ (B <= x < B + Sz)) -> find_segment rsegs x 1 = None.
Proof.
  intros x H. destruct (find_segment rsegs x 1) eqn:E; [|reflexivity]. exfalso.
  assert (Hs : find_segment rsegs x 1 <> None) by congruence.
  destruct (fs_some rsegs x 1 ltac:(lia) Hs) as (sg & Hin & Hr).
  apply (H (Z.of_N (seg_base sg)) (Z.of_N (seg_size sg))); [|exact Hr].
  rewrite <- segs_eq. apply in_map_iff. exists sg. split; [reflexivity | exact Hin].
Qed.

(** A present byte of such a block is in the overlay, so it is writable. *)
Lemma wr_at_block : forall m a bs, bytes_at rsegs m a bs -> blk_noimg rsegs a (Z.of_nat (length bs)) ->
  wr_at rsegs m a (Z.of_nat (length bs)).
Proof.
  intros m a bs (H0 & H1 & H) Hni. split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hr : mrd rsegs m (wa (a + i)) <> None).
  { replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. rewrite H by lia.
    intros C. apply nth_error_None in C. lia. }
  unfold mrd in Hr. unfold wview. destruct (m (wa (a + i))) as [b|]; [discriminate|].
  exfalso. apply Hr. apply (U.MemNorm.seg_rom_unmapped rsegs). apply res_none.
  intros B Sz Hin. unfold wa. rewrite unsigned_lit by lia. exact (noimg_res a _ Hni B Sz Hin i Hi).
Qed.

Lemma ro_str : forall m a l, mem_inv rsegs m -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  ro_bytes_b rsegs a l = true -> bytes_at rsegs m a l.
Proof. intros m a l MI H0 H1 H. apply ro_bytes_at; auto. apply ro_bytes_b_sound. exact H. Qed.

Definition FMT_AL : Z := 0x10338.   (* "%s:%d: " *)
Definition FMT_A : Z := 0x108c4.    (* "%s: " *)

Lemma fal_at : forall m, mem_inv rsegs m -> cstrz_at rsegs m FMT_AL F_addr_line.
Proof.
  intros m MI. exists (zb F_addr_line).
  split; [apply ro_str; [exact MI | unfold FMT_AL; lia | change (length (zb F_addr_line ++ [ZERO])) with 8%nat; unfold FMT_AL; lia
                        | vm_compute; reflexivity]|].
  split; [vm_compute; reflexivity | apply nulfree_forallb; vm_compute; reflexivity].
Qed.

Lemma fa_at : forall m, mem_inv rsegs m -> cstrz_at rsegs m FMT_A F_addr.
Proof.
  intros m MI. exists (zb F_addr).
  split; [apply ro_str; [exact MI | unfold FMT_A; lia | change (length (zb F_addr ++ [ZERO])) with 5%nat; unfold FMT_A; lia
                        | vm_compute; reflexivity]|].
  split; [vm_compute; reflexivity | apply nulfree_forallb; vm_compute; reflexivity].
Qed.

Lemma sbase_at : forall m, mem_inv rsegs m -> cstr_at rsegs m STR_BASE S_base.
Proof.
  intros m MI. exists (zb S_base), [].
  split; [apply ro_str; [exact MI | unfold STR_BASE; lia | change (length (zb S_base ++ [ZERO])) with 13%nat; unfold STR_BASE; lia
                        | vm_compute; reflexivity]|].
  split; [vm_compute; reflexivity|]. split; [apply nulfree_forallb; vm_compute; reflexivity|].
  change (length S_base) with 12%nat. unfold STR_BASE. vm_compute. intros H; discriminate H.
Qed.

Ltac ltb_false := match goal with |- context [?x <? ?y] => rewrite (proj2 (Z.ltb_ge x y)) by lia end.

(** * The walk *)
Section W.
Variables (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo ln : Z) (rc : rconf) (f : list Z) (args : list arg).
Hypothesis HSN : rf_snprintf.
Hypothesis HVSN : rf_vsnprintf.
Hypothesis Hc16 : bv_unsigned a0 mod 16 = 0.
Hypothesis HRC : rconf_at rsegs m (bv_unsigned a0) rc.
Hypothesis Hap : apart (bv_unsigned a0) SEG_C_SIZE lo (bv_unsigned sp).
Hypothesis Himg : blk_noimg rsegs (bv_unsigned a0) SEG_C_SIZE.
Hypothesis Hrf : rc_refused rc + 1 < 2 ^ 32.
Hypothesis Hln : 0 <= ln < 2 ^ 31.
Hypothesis Hline : bv_unsigned a1 = ln.
Hypothesis Hf : In f REFUSE_FORMATS.
Hypothesis Hck : conv_kinds f = map arg_is_s args.
Hypothesis Hfz : cstrz_at rsegs m (bv_unsigned a2) f.
Hypothesis Hro : RO_LO <= bv_unsigned a2.
Hypothesis Hfe : bv_unsigned a2 + Z.of_nat (length f) + 1 <= sa_ro_end SA.
Hypothesis Hva : va_args_ok rsegs m
  [(lo, bv_unsigned sp);
   (refusal_addr (bv_unsigned a0) (length (rc_refusal rc)),
    refusal_addr (bv_unsigned a0) (length (rc_refusal rc)) + RC_REFUSAL_LEN);
   (bv_unsigned a0 + RC_REFUSED, bv_unsigned a0 + RC_REFUSED + 4)] [a3; a4; a5; a6; a7] args.
Hypothesis Henv : printf_env m fc lo (bv_unsigned sp).
Hypothesis Hst : stack_ok rsegs m lo (bv_unsigned sp) REFUSE_STACK.
Hypothesis MI0 : mem_inv rsegs m.

Definition Post : machine_state -> Prop :=
  ret_void_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m (refuse_W (bv_unsigned sp) (bv_unsigned a0) rc) lo
    (fun m' => rconf_at rsegs m' (bv_unsigned a0) (refuse rc ln f args)).

(** The bytes written: the frame and printf's stack, refused, the slot, n_refusals. *)
Definition W2 : list ivl := [(bv_unsigned sp - 6032, bv_unsigned sp); (bv_unsigned a0 + 13516, bv_unsigned a0 + 13520)].


Definition DD : Z := bv_unsigned a0 + 11912 + 200 * Z.of_nat (length (rc_refusal rc)).
Definition KP : Z := snprintf_r (r_addr_fmt ln) (r_addr_args rc ln).
Definition PP : list Z := snprintf_s 200 (r_addr_fmt ln) (r_addr_args rc ln).
Definition TT : list Z := snprintf_s (200 - KP) f args.
Definition W3 : list ivl :=
  [(bv_unsigned sp - 6032, bv_unsigned sp); (bv_unsigned a0 + 13516, bv_unsigned a0 + 13520); (DD, DD + 200)].
Definition W4 : list ivl :=
  [(bv_unsigned sp - 6032, bv_unsigned sp); (bv_unsigned a0 + 13516, bv_unsigned a0 + 13520); (DD, DD + 200);
   (bv_unsigned a0 + 13512, bv_unsigned a0 + 13516)].

Ltac nums :=
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; change (bv_modulus 64) with (2 ^ 64) in Rsp;
  pose proof (bv_unsigned_in_range 64 a0) as Ra0; change (bv_modulus 64) with (2 ^ 64) in Ra0;
  pose proof Hap as Hap'; unfold apart, SEG_C_SIZE in Hap';
  pose proof Himg as Hni; unfold SEG_C_SIZE in Hni;
  pose proof Henv as (FRM & TM & SSP & HLOI & HSP63); unfold SA, SEG_UBSAN in HLOI; cbn [sa_img_end] in HLOI;
  pose proof Hst as (ST0 & HLO & HSP16 & HNR); unfold REFUSE_STACK, PRINTF_K in HLO;
  pose proof HRC as (bs0 & BC0 & HE0);
  pose proof HE0 as (HLc & _ & _ & _ & Hrl & _ & [Hn0 Hnref] & [Hr0 Hrref] & _);
  unfold SEG_C_SIZE in HLc.

(** Every byte refuse may write was present at entry. *)
Lemma pres4 : forall x : word, ~ outside W4 (bv_unsigned x) -> mrd rsegs m x <> None.
Proof.
  nums. intros x Hx. unfold W4, DD in Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as Rx.
  change (bv_modulus 64) with (2 ^ 64) in Rx.
  assert (E : wa (bv_unsigned x) = x) by (unfold wa; apply Z_to_bv_bv_unsigned).
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned sp)) as [Hlt|Hge].
  - destruct (Z_le_dec (bv_unsigned sp - 6032) (bv_unsigned x)) as [Hle|Hgt].
    + destruct ST0 as (_ & _ & STa). destruct (STa (bv_unsigned x) ltac:(lia)) as [_ (b & Hb)].
      rewrite E in Hb. rewrite Hb. discriminate.
    + assert (Hc : bv_unsigned a0 <= bv_unsigned x < bv_unsigned a0 + 16616) by lia.
      destruct BC0 as (_ & _ & Bb). rewrite <- E.
      replace (bv_unsigned x) with (bv_unsigned a0 + Z.of_nat (Z.to_nat (bv_unsigned x - bv_unsigned a0))) by lia.
      rewrite Bb by lia. intros C. apply nth_error_None in C. lia.
  - assert (Hc : bv_unsigned a0 <= bv_unsigned x < bv_unsigned a0 + 16616) by lia.
    destruct BC0 as (_ & _ & Bb). rewrite <- E.
    replace (bv_unsigned x) with (bv_unsigned a0 + Z.of_nat (Z.to_nat (bv_unsigned x - bv_unsigned a0))) by lia.
    rewrite Bb by lia. intros C. apply nth_error_None in C. lia.
Qed.

(** The epilogue from 0x15648: the four reloads, sp back, ret. *)
Lemma epi : forall mk Fk fck j0 j1 W (x1 y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 u3 u4 u5 u6 : word),
  rw_cells rsegs mk (bv_unsigned sp + -96) [CB 16 j0; C8 s2; C8 s1; C8 s0; C8 ra; CB 48 j1] ->
  stk rsegs mk lo (bv_unsigned sp + -96) -> mem_inv rsegs mk -> wmono rsegs m mk -> munch W m mk ->
  sub_fp W (refuse_W (bv_unsigned sp) (bv_unsigned a0) rc) ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd rsegs m x <> None) ->
  frm0 fck -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Fk k = reg_get F k) ->
  rconf_at rsegs mk (bv_unsigned a0) (refuse rc ln f args) ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7
                       w18 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                     Fk (Z_to_bv 64 0x15d98) fck None mk (seg_rom rsegs)).
Proof.
  intros mk Fk fck j0 j1 W x1 y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 u3 u4 u5 u6 FR ST MI WM MU SUB PRES FRk FEQ Q.
  nums.
  assert (TMk : U.MemNorm.task_mem rsegs mk) by exact (task_mem_munch rsegs W m mk TM MU PRES).
  assert (MUk : munch (refuse_W (bv_unsigned sp) (bv_unsigned a0) rc) m mk) by exact (munch_weaken W _ m mk SUB MU).
  clear MU SUB PRES.
  do 5 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.

Lemma reading_facts : Forall zbyte (rc_reading rc) /\ (length (rc_reading rc) < 96)%nat /\ nulfree (rc_reading rc).
Proof.
  destruct HRC as (bs & _ & HE). destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hl0 & Hs0 & Hn0 & Hf0) & _).
  split; [|split; [exact Hs0 | exact Hn0]].
  assert (Hz : Forall zbyte (rc_reading rc ++ [0])) by (rewrite <- Hf0; apply Forall_firstn_gen, zs_byte).
  apply Forall_app in Hz. exact (proj1 Hz).
Qed.

Lemma where_facts : Forall zbyte (r_where rc) /\ (length (r_where rc) <= 95)%nat /\ nulfree (r_where rc).
Proof.
  pose proof reading_facts as (Hb & Hl & Hn). unfold r_where.
  destruct (hd0 (rc_reading rc) =? 0).
  - split; [apply zbyte_forallb; vm_compute; reflexivity|].
    split; [change (length S_base) with 12%nat; lia | apply nulfree_forallb; vm_compute; reflexivity].
  - split; [exact Hb|]. split; [lia | exact Hn].
Qed.

Lemma dec_len10 : forall z, 0 <= z < 2 ^ 31 -> (length (dec z) <= 10)%nat.
Proof.
  intros z H. unfold dec. destruct (Z.ltb_spec z 0); [lia|].
  pose proof (dec_go_len 9 20 z [] ltac:(cbn; lia) ltac:(lia)) as Hd. cbn [length] in Hd. lia.
Qed.

Lemma fmt_addr_facts : Forall zbyte (fmt (r_addr_fmt ln) (r_addr_args rc ln)) /\
  nulfree (fmt (r_addr_fmt ln) (r_addr_args rc ln)) /\ (length (fmt (r_addr_fmt ln) (r_addr_args rc ln)) <= 108)%nat.
Proof.
  pose proof where_facts as (Hb & Hl & Hn). pose proof (dec_len10 ln Hln) as Hd.
  unfold r_addr_fmt, r_addr_args. destruct (0 <? ln).
  - rewrite fmt_addr_line, (cut_nul_id _ Hn). split; [|split].
    + apply Forall_app; split; [exact Hb|]. apply Forall_app; split; [apply zbyte_forallb; reflexivity|].
      apply Forall_app; split; [apply dec_byte | apply zbyte_forallb; reflexivity].
    + apply nulfree_app; split; [exact Hn|]. apply nulfree_app; split; [apply nulfree_forallb; reflexivity|].
      apply nulfree_app; split; [apply dec_nulfree | apply nulfree_forallb; reflexivity].
    + rewrite !length_app. cbn [length]. lia.
  - rewrite fmt_addr, (cut_nul_id _ Hn). split; [|split].
    + apply Forall_app; split; [exact Hb | apply zbyte_forallb; reflexivity].
    + apply nulfree_app; split; [exact Hn | apply nulfree_forallb; reflexivity].
    + rewrite !length_app. cbn [length]. lia.
Qed.

Lemma KP_facts : 0 <= KP <= 108 /\ length PP = Z.to_nat KP /\ Forall zbyte PP /\ nulfree PP.
Proof.
  pose proof fmt_addr_facts as (Hb & Hn & Hl). unfold KP, PP, snprintf_r, snprintf_s.
  rewrite firstn_all2 by (change (Z.to_nat (200 - 1)) with 199%nat; lia).
  split; [lia|]. split; [lia|]. split; assumption.
Qed.

Lemma TT_facts : (length TT <= Z.to_nat (199 - KP))%nat /\ Forall zbyte TT /\ nulfree TT.
Proof.
  destruct (refuse_formats_ok f Hf) as [Hn Hb]. pose proof (va_args_argb _ _ _ _ _ Hva) as Ha.
  unfold TT, snprintf_s. split; [rewrite length_firstn; lia|].
  split; [apply Forall_firstn_gen, (fmt_byte_n (length f)); auto | apply nulfree_firstn, fmt_nulfree, Hn].
Qed.

Lemma refuse_kept : (length (rc_refusal rc) < 8)%nat ->
  refuse rc ln f args = RConf (rc_seg rc) (rc_refusal rc ++ [PP ++ TT]) (rc_refused rc + 1) (rc_overflow rc)
                              (rc_reading rc) (rc_gen rc).
Proof.
  intros H. pose proof KP_facts as (HK & _). unfold refuse. cbv zeta.
  change (snprintf_r (r_addr_fmt ln) (r_addr_args rc ln)) with KP.
  change (snprintf_s 200 (r_addr_fmt ln) (r_addr_args rc ln)) with PP.
  change (snprintf_s (200 - KP) f args) with TT.
  rewrite (proj2 (Z.leb_gt 8 (Z.of_nat (length (rc_refusal rc))))) by lia.
  rewrite (proj2 (Z.ltb_ge KP 0)) by lia. rewrite (proj2 (Z.leb_gt 200 KP)) by lia. reflexivity.
Qed.

(** From 0x15610, when snprintf has returned k = KP and written PP and its NUL at the slot. *)
Lemma after1 : forall m2 F2 fc2 j0 j1 P1 SL P3 NR R Q3 (y1 y5 y6 y7 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 : word),
  rw_cells rsegs m2 (bv_unsigned sp + -96)
    [CB 16 j0; C8 s2; C8 s1; C8 s0; C8 ra; CB 8 j1; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
  stk rsegs m2 lo (bv_unsigned sp + -96) ->
  bytes_at rsegs m2 (bv_unsigned a0) P1 -> bytes_at rsegs m2 DD (zb PP ++ [ZERO]) ->
  bytes_at rsegs m2 (DD + KP + 1) (skipn (Z.to_nat KP + 1) SL) -> bytes_at rsegs m2 (DD + 200) P3 ->
  bytes_at rsegs m2 (bv_unsigned a0 + 13512) NR ->
  bytes_at rsegs m2 (bv_unsigned a0 + 13516) (le4 (Z_to_bv 64 (rc_refused rc + 1))) ->
  bytes_at rsegs m2 (bv_unsigned a0 + 13520) Q3 ->
  wr_at rsegs m2 (bv_unsigned a0) 16616 ->
  munch W3 m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 -> frm0 fc2 ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F2 k = reg_get F k) ->
  rconf_enc rc (P1 ++ SL ++ P3 ++ NR ++ R ++ Q3) ->
  Z.of_nat (length P1) = 11912 + 200 * Z.of_nat (length (rc_refusal rc)) -> length SL = 200%nat ->
  length NR = 4%nat -> length R = 4%nat -> Z.of_nat (length Q3) = 3096 ->
  NR = le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc)))) -> (length (rc_refusal rc) < 8)%nat ->
  evt rsegs Post (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y5 y6 y7 a2 (Z_to_bv 64 DD) (Z_to_bv 64 KP)
                       z1 z2 z3 z4 z5 z6 z7 (Z_to_bv 64 (bv_unsigned a0 + 13512)) s3 s4 s5 s6 s7 s8 s9 s10 s11
                       u3 u4 u5 u6)
                     F2 (Z_to_bv 64 0x15d54) fc2 None m2 (seg_rom rsegs)).
Proof.
  intros m2 F2 fc2 j0 j1 P1 SL P3 NR R Q3 y1 y5 y6 y7 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6
    FR ST BP1 BPF BSL2 B3 BN BRF BQ3 WC MU WM MI FRM2 FEQ HE LP1 LSL LNR LR LQ3 ENR Hn8.
  nums. pose proof KP_facts as (HK & HLP & HBP & HNP). pose proof TT_facts as (HLT & HBT & HNT).
  assert (HDD : DD = bv_unsigned a0 + 11912 + 200 * Z.of_nat (length (rc_refusal rc))) by reflexivity.
  unfold W3 in MU. pose proof (bytes_at_bound _ _ _ _ BQ3) as BBq. rewrite LQ3 in BBq.
  assert (LZB : length (zb PP) = Z.to_nat KP) by (rewrite length_zb; exact HLP).
  assert (LSK : length (skipn (Z.to_nat KP + 1) SL) = (199 - Z.to_nat KP)%nat) by (rewrite length_skipn; lia).
  assert (LP3 : Z.of_nat (length P3) = 1400 - 200 * Z.of_nat (length (rc_refusal rc))).
  { pose proof HE as (HLt & _). rewrite !length_app in HLt. unfold SEG_C_SIZE in HLt. lia. }
  zstep. zstep. ltu_rw. rewrite (proj2 (Z.ltb_ge 199 KP)) by lia. cbv iota.
  zstep. zstep. zstep. zstep.
  rewrite (zb_lxor_ones DD) by lia. ltu_rw. ltb_false. cbv iota.
  do 7 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  rewrite (bv_swrap_small 32 (200 - KP)) by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  destruct (stk_split rsegs m3 lo (bv_unsigned sp - 6032) (bv_unsigned sp + -96) ST ltac:(lia)) as [STlo STpf].
  clear ST.
  (* the slot after PP: its NUL at DD + KP, then SL's bytes; vsnprintf overwrites [DD + KP, DD + KP + |TT| + 1) *)
  apply bytes_at_app in BPF as [BPP BZ]. rewrite length_zb, HLP, Z2Nat.id in BZ by lia.
  assert (BJ : bytes_at rsegs m3 (DD + KP) ([ZERO] ++ skipn (Z.to_nat KP + 1) SL)).
  { apply bytes_at_app. split; [exact BZ|]. cbn [length]. replace (DD + KP + Z.of_nat 1) with (DD + KP + 1) by lia.
    exact BSL2. }
  assert (LTs : (length TT <= length (skipn (Z.to_nat KP + 1) SL))%nat) by (rewrite length_skipn; lia).
  rewrite <- (firstn_skipn (length TT) (skipn (Z.to_nat KP + 1) SL)) in BSL2.
  apply bytes_at_app in BSL2 as [_ BREST]. rewrite length_firstn, Nat.min_l in BREST by exact LTs.
  set (REST := skipn (length TT) (skipn (Z.to_nat KP + 1) SL)) in BREST.
  assert (LREST : length REST = (199 - Z.to_nat KP - length TT)%nat) by (unfold REST; rewrite !length_skipn; lia).
  pose proof (rw_tail rsegs m3 _ [CB 8 _; C8 _; C8 s2; C8 s1; C8 s0; C8 ra; CB 8 _] [C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] FR)
    as SV.
  cbn [cells_size csize Nat.add] in SV.
  pose proof HVSN as V. unfold rf_vsnprintf, RF_VSNPRINTF in V.
  assert (Lf : forall bf, zs bf = f -> length bf = length f) by (intros bf Hz; rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  pose proof Hfe as Hfe'. unfold SA, SEG_UBSAN in Hfe'. cbn [sa_ro_end] in Hfe'.
  eapply evt_cut.
  { eapply V with (lo := bv_unsigned sp - 6032) (Dslot := DD) (f := f) (slots := [a3; a4; a5; a6; a7]) (args := args);
      rewrite ?unsigned_lit by lia.
    - (* rf_fmt *)
      split; [exact Hf|]. split; [exact Hck|]. split.
      { destruct Hfz as (bf & Bf & Hz & Hn). exists bf. split; [|split; assumption].
        eapply bytes_at_transport; [exact Bf | exact MU |]. rewrite length_app, (Lf bf Hz). cbn [disjoint_from length].
        unfold RO_LO in Hro.
        pose proof (noimg_disj _ _ 0x10000 0x3000 (bv_unsigned a2) (Z.of_nat (length f) + 1) (bv_unsigned a0 + 13516) 4 Hni
                      ltac:(unfold RES; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as D1.
        pose proof (noimg_disj _ _ 0x10000 0x3000 (bv_unsigned a2) (Z.of_nat (length f) + 1) DD 200 Hni
                      ltac:(unfold RES; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as D2.
        split; [lia | split; [lia | split; [lia | exact I]]]. }
      split; [exact Hro|]. split; [exact Hfe|].
      apply (va_args_munch rsegs m m3 _ _ _ _ _ Hva MU). intros a n Hn H.
      apply apart_all3 in H as (H1 & H2 & H3).
      unfold apart, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_REFUSED in H1, H2, H3.
      split; [cbn [disjoint_from]; split; [lia | split; [lia | split; [lia | exact I]]]|].
      apply apart_all2; unfold apart, RC_REFUSAL_LEN; lia.
    - (* the saved slots a3 .. a7 *)
      unfold saved_at. replace (bv_unsigned sp + -40) with (bv_unsigned sp + -96 + Z.of_nat 56) by lia. exact SV.
    - lia.
    - cbn [length]. lia.
    - (* the destination dst + k, 200 - k *)
      unfold rf_dst. cbn [length]. unfold RC_REFUSAL_LEN.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply (noimg_sub _ _ _ _ Hni); lia|].
      split; [apply (wr_at_sub rsegs m3 _ _ _ _ WC); lia|].
      split; [exists ([ZERO] ++ skipn (Z.to_nat KP + 1) SL); split; [exact BJ | rewrite length_app, length_skipn; cbn [length]; lia]|].
      unfold apart. lia.
    - (* printf_env *)
      split; [exact FRM2|].
      split; [apply (task_mem_munch rsegs _ m m3 TM MU); intros x Hx; apply pres4; unfold W4; cbn [outside] in *;
              intros (H1 & H2 & H3 & H4 & _); apply Hx; split; [exact H1 | split; [exact H2 | split; [exact H3 | exact I]]]|].
      split.
      { destruct SSP as [G1 (g & G2)]. unfold ssp_ok. unfold SA, SEG_UBSAN in G1, G2 |- *. cbn [sa_got_guard sa_guard] in G1, G2 |- *.
        pose proof (noimg_disj _ _ 0x21000 0x2000 0x221b0 8 (bv_unsigned a0 + 13516) 4 Hni
                      ltac:(unfold RES; right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia)) as D1.
        pose proof (noimg_disj _ _ 0x21000 0x2000 0x221b0 8 DD 200 Hni
                      ltac:(unfold RES; right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia)) as D2.
        pose proof (noimg_disj _ _ 0x23000 0x32000 0x53820 8 (bv_unsigned a0 + 13516) 4 Hni
                      ltac:(unfold RES; right; right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(lia)) as D3.
        pose proof (noimg_disj _ _ 0x23000 0x32000 0x53820 8 DD 200 Hni
                      ltac:(unfold RES; right; right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(lia)) as D4.
        split; [apply (bytes_at_transport rsegs _ m m3 _ _ G1 MU) | exists g; apply (bytes_at_transport rsegs _ m m3 _ _ G2 MU)];
          (rewrite length_le8; cbn [disjoint_from]; split; [lia | split; [lia | split; [lia | exact I]]]). }
      unfold SA, SEG_UBSAN. cbn [sa_img_end]. split; lia.
    - (* stack_ok *)
      unfold stack_ok, PRINTF_K. split; [exact STpf|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
      intros a Ha. apply HNR. lia.
    - exact MI. }
  intros ms' PO. unfold rf_post, ret_post_fp in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F3 & fc3 & m4 &
                  E & FRM3 & FEQ3 & MU3 & WM3 & MI3 & TM3 & ST3 & BT).
  subst ms'. ret_lit.
  rewrite ?unsigned_lit in MU3, ST3, BT by lia.
  rewrite (unsigned_lit (DD + KP)) in MU3 by lia.
  rewrite (unsigned_lit (200 - KP)) in MU3, BT by lia.
  change (snprintf_s (200 - KP) f args) with TT in MU3, BT.
  assert (DJ : forall A n, bv_unsigned a0 <= A -> A + n <= bv_unsigned a0 + 16616 ->
            A + n <= DD + KP \/ DD + KP + Z.of_nat (length TT) + 1 <= A ->
            disjoint_from [(bv_unsigned sp - 6032, bv_unsigned sp + -96); (DD + KP, DD + KP + Z.of_nat (length TT) + 1)] A n)
    by (intros A n0 HA1 HA2 HA3; cbn [disjoint_from]; split; [lia | split; [lia | exact I]]).
  pose proof (bytes_at_transport rsegs _ m3 m4 _ _ BP1 MU3 ltac:(apply DJ; lia)) as BP1'.
  pose proof (bytes_at_transport rsegs _ m3 m4 _ _ BPP MU3 ltac:(apply DJ; rewrite ?LZB; lia)) as BPP'.
  pose proof (bytes_at_transport rsegs _ m3 m4 _ _ BREST MU3 ltac:(apply DJ; rewrite ?LREST; lia)) as BREST'.
  pose proof (bytes_at_transport rsegs _ m3 m4 _ _ B3 MU3 ltac:(apply DJ; lia)) as B3'.
  pose proof (bytes_at_transport rsegs _ m3 m4 _ _ BN MU3 ltac:(apply DJ; rewrite ?LNR; lia)) as BN'.
  pose proof (bytes_at_transport rsegs _ m3 m4 _ _ BRF MU3 ltac:(apply DJ; rewrite ?length_le4; lia)) as BRF'.
  pose proof (bytes_at_transport rsegs _ m3 m4 _ _ BQ3 MU3 ltac:(apply DJ; lia)) as BQ3'.
  pose proof (rw_cells_transport rsegs _ m3 m4 _ _ FR MU3 WM3
                ltac:(cbn [cells_size csize Nat.add disjoint_from]; split; [lia | split; [lia | exact I]])) as FR'.
  pose proof (stk_transport_disjoint rsegs _ m3 m4 _ _ STlo MU3 WM3
                ltac:(cbn [disjoint_from]; split; [lia | split; [lia | exact I]])) as STlo'.
  pose proof (stk_merge rsegs m4 lo (bv_unsigned sp - 6032) (bv_unsigned sp + -96) STlo' ST3 ltac:(lia)) as ST4.
  pose proof (wr_at_transport rsegs m3 m4 _ _ WC WM3) as WC'.
  assert (MU4 : munch [(bv_unsigned sp - 6032, bv_unsigned sp); (bv_unsigned a0 + 13516, bv_unsigned a0 + 13520);
                       (DD, DD + 200); (bv_unsigned a0 + 13512, bv_unsigned a0 + 13516)] m m4).
  { eapply munch_trans; [|eapply munch_weaken; [|exact MU3]].
    - eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside].
      intros x (H1 & H2 & H3 & H4 & _). split; [exact H1 | split; [exact H2 | split; [exact H3 | exact I]]].
    - unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & H4 & _). split; [lia | split; [lia | exact I]]. }
  pose proof (wmono_trans rsegs _ _ _ WM WM3) as WM4.
  clear BP1 BPP BREST B3 BN BRF BQ3 FR STlo ST3 STlo' WC MU MU3 WM WM3 SV BJ BZ STpf.
  assert (RD : ov_read_bytes rsegs m4 (wa (bv_unsigned a0 + 13512)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc)))))).
  { rewrite <- ENR. replace (bv_unsigned a0 + 13512) with (bv_unsigned a0 + 13512 + 0) by lia.
    rewrite (bytes_at_read rsegs m4 _ NR 0 4 BN') by lia. change (skipn (Z.to_nat 0) NR) with NR.
    rewrite firstn_all2 by (rewrite LNR; constructor). reflexivity. }
  zstep.
  rewrite (sx32_small (Z.of_nat (length (rc_refusal rc)))) by lia.
  zstep.
  rewrite (bv_swrap_small 32 (Z.of_nat (length (rc_refusal rc)) + 1)) by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  zstep. lts_rw. ltb_false. cbv iota.
  pose proof (wr_at_store_ok rsegs m4 (bv_unsigned a0) 16616 13512 4 WC' ltac:(lia) ltac:(lia)) as SO.
  assert (LZT : length (zb TT) = length TT) by apply length_zb.
  clear RD BN'.
  step.
  pose proof (bytes_at_write_same rsegs m4 (bv_unsigned a0 + 13512)
                (le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc)) + 1))) ltac:(lia) ltac:(rewrite length_le4; lia)) as BNn.
  store_done.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
  apply (rw_cells_merge rsegs m5 _ [CB 8 _; C8 _; C8 s2; C8 s1; C8 s0; C8 ra] [CB 8 _; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] [])
    in FR'.
  apply (rw_cells_merge rsegs m5 _ [] [CB 8 _; C8 _] _) in FR'.
  cbn [app cells_size csize Nat.add] in FR'.
  eapply epi; [exact FR' | exact ST4 | exact MI3 | exact WM4 | exact MU4 | | | exact FRM3 | | ].
  - unfold sub_fp, refuse_W, REFUSE_STACK, PRINTF_K, RC_REFUSED, RC_NREF, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN.
    rewrite (proj2 (Nat.ltb_lt _ _) Hn8). cbn [outside app].
    intros x (H1 & H2 & H3 & H4 & _). split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]].
  - intros x Hx. apply pres4. unfold W4. exact Hx.
  - intros k Hk. rewrite FEQ3 by exact Hk. apply FEQ. exact Hk.
  - rewrite refuse_kept by exact Hn8.
    exists (P1 ++ (zb (PP ++ TT) ++ [ZERO] ++ REST) ++ P3 ++ le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc)) + 1)) ++
            le4 (Z_to_bv 64 (rc_refused rc + 1)) ++ Q3).
    split.
    + apply bytes_at_app. split; [exact BP1'|].
      replace (bv_unsigned a0 + Z.of_nat (length P1)) with DD by lia.
      apply bytes_at_app. split.
      { rewrite zb_app, <- app_assoc. apply bytes_at_app. split; [exact BPP'|]. rewrite LZB, Z2Nat.id by lia.
        rewrite app_assoc. apply bytes_at_app. split; [exact BT|]. rewrite length_app, LZT. cbn [length].
        replace (DD + KP + Z.of_nat (length TT + 1)) with (DD + KP + 1 + Z.of_nat (length TT)) by lia. exact BREST'. }
      replace (DD + Z.of_nat (length (zb (PP ++ TT) ++ [ZERO] ++ REST))) with (DD + 200)
        by (rewrite !length_app, length_zb, length_app; cbn [length]; lia).
      apply bytes_at_app. split; [exact B3'|].
      replace (DD + 200 + Z.of_nat (length P3)) with (bv_unsigned a0 + 13512) by lia.
      apply bytes_at_app. split; [exact BNn|]. rewrite length_le4.
      replace (bv_unsigned a0 + 13512 + Z.of_nat 4) with (bv_unsigned a0 + 13516) by lia.
      apply bytes_at_app. split; [exact BRF'|]. rewrite length_le4.
      replace (bv_unsigned a0 + 13516 + Z.of_nat 4) with (bv_unsigned a0 + 13520) by lia. exact BQ3'.
    + apply (enc_kept rc P1 SL P3 NR R Q3 (PP ++ TT) REST HE LP1 LSL LNR LR LQ3 Hn8 Hrf).
      * apply Forall_app; split; assumption.
      * apply nulfree_app; split; assumption.
      * rewrite length_app. lia.
      * rewrite LREST, length_app. lia.
Qed.


(** snprintf(dst, 200, fmt, where[, line]) at 0x19a14 and its return to 0x15d3c (line > 0: then `j 0x15d54`) or
    0x15d54 (line = 0). *)
Lemma snp_call : forall (b : bool) m1 j0 j1 P1 SL P3 NR R Q3 w fpa (y4 y5 t1 t2 t3 t4 t5 t6 : word),
  b = (0 <? ln) -> fpa = (if b then FMT_AL else FMT_A) -> (b = true -> y4 = Z_to_bv 64 ln) ->
  rw_cells rsegs m1 (bv_unsigned sp + -96)
    [CB 16 j0; C8 s2; C8 s1; C8 s0; C8 ra; CB 8 j1; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
  stk rsegs m1 lo (bv_unsigned sp + -96) ->
  bytes_at rsegs m1 (bv_unsigned a0) P1 -> bytes_at rsegs m1 DD SL -> bytes_at rsegs m1 (DD + 200) P3 ->
  bytes_at rsegs m1 (bv_unsigned a0 + 13512) NR ->
  bytes_at rsegs m1 (bv_unsigned a0 + 13516) (le4 (Z_to_bv 64 (rc_refused rc + 1))) ->
  bytes_at rsegs m1 (bv_unsigned a0 + 13520) Q3 ->
  wr_at rsegs m1 (bv_unsigned a0) 16616 ->
  munch W2 m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rconf_enc rc (P1 ++ SL ++ P3 ++ NR ++ R ++ Q3) ->
  Z.of_nat (length P1) = 11912 + 200 * Z.of_nat (length (rc_refusal rc)) -> length SL = 200%nat ->
  length NR = 4%nat -> length R = 4%nat -> Z.of_nat (length Q3) = 3096 ->
  NR = le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc)))) -> (length (rc_refusal rc) < 8)%nat ->
  w <> 0 -> 0 <= w < 2 ^ 64 -> cstr_at rsegs m1 w (r_where rc) ->
  apart_all w (Z.of_nat (length (r_where rc)) + 8) [(bv_unsigned sp - 6032, bv_unsigned sp + -96); (DD, DD + 200)] ->
  evt rsegs Post (MS (mkR (Z_to_bv 64 (if b then 0x15d3c else 0x15d54)) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp
                       (Z_to_bv 64 ln) t1 t2 a2 (Z_to_bv 64 DD) (Z_to_bv 64 DD) (Z_to_bv 64 200) (Z_to_bv 64 fpa)
                       (Z_to_bv 64 w) y4 y5 a6 a7 (Z_to_bv 64 (bv_unsigned a0 + 13512))
                       s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x19a14) fc None m1 (seg_rom rsegs)).
Proof.
  intros b m1 j0 j1 P1 SL P3 NR R Q3 w fpa y4 y5 t1 t2 t3 t4 t5 t6 Eb Efp Ey4
    FR ST BP1 BSL B3 BN BRF BQ3 WC MU WM MI HE LP1 LSL LNR LR LQ3 ENR Hn8 Hw0 Hwr Hwc Hwa.
  nums. pose proof KP_facts as (HK & HLP & HBP & HNP). pose proof where_facts as (_ & HLW & _).
  assert (HDD : DD = bv_unsigned a0 + 11912 + 200 * Z.of_nat (length (rc_refusal rc))) by reflexivity.
  unfold W2 in MU. pose proof (bytes_at_bound _ _ _ _ BQ3) as BBq. rewrite LQ3 in BBq.
  assert (LP3 : Z.of_nat (length P3) = 1400 - 200 * Z.of_nat (length (rc_refusal rc))).
  { pose proof HE as (HLt & _). rewrite !length_app in HLt. unfold SEG_C_SIZE in HLt. lia. }
  pose proof BSL as BSL0.
  rewrite <- (firstn_skipn (Z.to_nat KP + 1) SL) in BSL. apply bytes_at_app in BSL as [_ BSL2].
  rewrite length_firstn, Nat.min_l in BSL2 by lia.
  replace (DD + Z.of_nat (Z.to_nat KP + 1)) with (DD + KP + 1) in BSL2 by lia.
  destruct (stk_split rsegs m1 lo (bv_unsigned sp - 6032) (bv_unsigned sp + -96) ST ltac:(lia)) as [STlo STpf].
  clear ST.
  assert (HFP : 0x10000 <= fpa <= 0x108c4) by (subst fpa; destruct b; unfold FMT_AL, FMT_A; lia).
  pose proof HSN as V. unfold rf_snprintf, RF_SNPRINTF in V.
  eapply evt_cut.
  { eapply V with (lo := bv_unsigned sp - 6032) (Dslot := DD) (f := r_addr_fmt ln) (args := r_addr_args rc ln);
      rewrite ?unsigned_lit by lia.
    - (* rf_fmt: the prefix format and where (and line) *)
      unfold r_addr_fmt, r_addr_args. rewrite <- Eb. subst fpa.
      destruct b.
      + split; [left; reflexivity|]. split; [reflexivity|]. split; [exact (fal_at m1 MI)|].
        split; [unfold RO_LO, FMT_AL; lia|].
        split; [unfold SA, SEG_UBSAN, FMT_AL; cbn [sa_ro_end]; change (length F_addr_line) with 7%nat; lia|].
        rewrite (Ey4 eq_refl). cbn [va_args_ok va_arg_ok]. rewrite ?unsigned_lit by lia. unfold RC_REFUSAL_LEN.
        split; [split; [exact Hw0 | split; [exact Hwc | split; [apply le_65535; exact HLW | exact Hwa]]]|].
        split; [split; [lia | reflexivity] | exact I].
      + split; [right; left; reflexivity|]. split; [reflexivity|]. split; [exact (fa_at m1 MI)|].
        split; [unfold RO_LO, FMT_A; lia|].
        split; [unfold SA, SEG_UBSAN, FMT_A; cbn [sa_ro_end]; change (length F_addr) with 4%nat; lia|].
        cbn [va_args_ok va_arg_ok]. rewrite ?unsigned_lit by lia. unfold RC_REFUSAL_LEN.
        split; [split; [exact Hw0 | split; [exact Hwc | split; [apply le_65535; exact HLW | exact Hwa]]] | exact I].
    - (* the slot *)
      unfold rf_dst, RC_REFUSAL_LEN.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply (noimg_sub _ _ _ _ Hni); lia|].
      split; [apply (wr_at_sub rsegs m1 _ _ _ _ WC); lia|].
      split; [exists SL; split; [exact BSL0 | rewrite LSL; reflexivity]|].
      unfold apart. lia.
    - (* printf_env *)
      split; [exact FRM|].
      split; [apply (task_mem_munch rsegs _ m m1 TM MU); intros x Hx; apply pres4; unfold W4; cbn [outside] in *;
              intros (H1 & H2 & H3 & H4 & _); apply Hx; split; [exact H1 | split; [exact H2 | exact I]]|].
      split.
      { destruct SSP as [G1 (g & G2)]. unfold ssp_ok. unfold SA, SEG_UBSAN in G1, G2 |- *.
        cbn [sa_got_guard sa_guard] in G1, G2 |- *.
        pose proof (noimg_disj _ _ 0x21000 0x2000 0x221b0 8 (bv_unsigned a0 + 13516) 4 Hni
                      ltac:(unfold RES; right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia)) as D1.
        pose proof (noimg_disj _ _ 0x23000 0x32000 0x53820 8 (bv_unsigned a0 + 13516) 4 Hni
                      ltac:(unfold RES; right; right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(lia)) as D3.
        split; [apply (bytes_at_transport rsegs _ m m1 _ _ G1 MU) | exists g; apply (bytes_at_transport rsegs _ m m1 _ _ G2 MU)];
          (rewrite length_le8; cbn [disjoint_from]; split; [lia | split; [lia | exact I]]). }
      unfold SA, SEG_UBSAN. cbn [sa_img_end]. split; lia.
    - (* stack_ok *)
      unfold stack_ok, PRINTF_K. split; [exact STpf|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
      intros a Ha. apply HNR. lia.
    - exact MI. }
  intros ms' PO. unfold rf_post, ret_post_fp in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F2 & fc2 & m2 &
                  E & FRM2 & FEQ2 & MU2 & WM2 & MI2 & TM2 & ST2 & BT).
  subst ms'.
  rewrite ?unsigned_lit in MU2, ST2, BT by lia.
  try rewrite (unsigned_lit (bv_unsigned sp + -96)) in MU2 by lia.
  try rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST2 by lia.
  try rewrite (unsigned_lit DD) in MU2 by lia. try rewrite (unsigned_lit DD) in BT by lia.
  try rewrite (unsigned_lit 200) in MU2 by lia. try rewrite (unsigned_lit 200) in BT by lia.
  change (snprintf_s 200 (r_addr_fmt ln) (r_addr_args rc ln)) with PP in MU2, BT.
  change (snprintf_r (r_addr_fmt ln) (r_addr_args rc ln)) with KP.
  rewrite HLP, Z2Nat.id in MU2 by lia.
  assert (DJ : forall A n, bv_unsigned a0 <= A -> A + n <= bv_unsigned a0 + 16616 ->
            A + n <= DD \/ DD + KP + 1 <= A ->
            disjoint_from [(bv_unsigned sp - 6032, bv_unsigned sp + -96); (DD, DD + KP + 1)] A n)
    by (intros A n0 HA1 HA2 HA3; cbn [disjoint_from]; split; [lia | split; [lia | exact I]]).
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ BP1 MU2 ltac:(apply DJ; lia)) as BP1'.
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ BSL2 MU2 ltac:(apply DJ; rewrite ?length_skipn; lia)) as BSL2'.
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ B3 MU2 ltac:(apply DJ; lia)) as B3'.
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ BN MU2 ltac:(apply DJ; rewrite ?LNR; lia)) as BN'.
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ BRF MU2 ltac:(apply DJ; rewrite ?length_le4; lia)) as BRF'.
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ BQ3 MU2 ltac:(apply DJ; lia)) as BQ3'.
  pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2
                ltac:(cbn [cells_size csize Nat.add disjoint_from]; split; [lia | split; [lia | exact I]])) as FR'.
  pose proof (stk_transport_disjoint rsegs _ m1 m2 _ _ STlo MU2 WM2
                ltac:(cbn [disjoint_from]; split; [lia | split; [lia | exact I]])) as STlo'.
  pose proof (stk_merge rsegs m2 lo (bv_unsigned sp - 6032) (bv_unsigned sp + -96) STlo' ST2 ltac:(lia)) as ST2'.
  pose proof (wr_at_transport rsegs m1 m2 _ _ WC WM2) as WC'.
  assert (MU3 : munch W3 m m2).
  { unfold W3. eapply munch_trans; [|eapply munch_weaken; [|exact MU2]].
    - eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside].
      intros x (H1 & H2 & H3 & _). split; [exact H1 | split; [exact H2 | exact I]].
    - unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _). split; [lia | split; [lia | exact I]]. }
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3.
  clear BP1 BSL2 B3 BN BRF BQ3 FR STlo ST2 STlo' WC MU MU2 WM WM2 BSL0.
  destruct b; cbv beta iota; [ret_lit; zstep|ret_lit];
    (eapply after1; [exact FR' | exact ST2' | exact BP1' | exact BT | exact BSL2' | exact B3' | exact BN' | exact BRF'
                    | exact BQ3' | exact WC' | exact MU3 | exact WM3 | exact MI2 | exact FRM2
                    | intros k Hk; rewrite FEQ2 by exact Hk; reflexivity
                    | exact HE | exact LP1 | exact LSL | exact LNR | exact LR | exact LQ3 | exact ENR | exact Hn8]).
Qed.


(** From 0x15d1c, where (a3) chosen: dst = c + 0x2e88 + 200 n (s1), then `blez line` picks the prefix format. *)
Lemma call1 : forall m1 j0 j1 P1 SL P3 NR R Q3 w (y10 y12 t1 t2 t3 t4 t5 t6 : word),
  rw_cells rsegs m1 (bv_unsigned sp + -96)
    [CB 16 j0; C8 s2; C8 s1; C8 s0; C8 ra; CB 8 j1; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
  stk rsegs m1 lo (bv_unsigned sp + -96) ->
  bytes_at rsegs m1 (bv_unsigned a0) P1 -> bytes_at rsegs m1 DD SL -> bytes_at rsegs m1 (DD + 200) P3 ->
  bytes_at rsegs m1 (bv_unsigned a0 + 13512) NR ->
  bytes_at rsegs m1 (bv_unsigned a0 + 13516) (le4 (Z_to_bv 64 (rc_refused rc + 1))) ->
  bytes_at rsegs m1 (bv_unsigned a0 + 13520) Q3 ->
  wr_at rsegs m1 (bv_unsigned a0) 16616 ->
  munch W2 m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rconf_enc rc (P1 ++ SL ++ P3 ++ NR ++ R ++ Q3) ->
  Z.of_nat (length P1) = 11912 + 200 * Z.of_nat (length (rc_refusal rc)) -> length SL = 200%nat ->
  length NR = 4%nat -> length R = 4%nat -> Z.of_nat (length Q3) = 3096 ->
  NR = le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc)))) -> (length (rc_refusal rc) < 8)%nat ->
  w <> 0 -> 0 <= w < 2 ^ 64 -> cstr_at rsegs m1 w (r_where rc) ->
  apart_all w (Z.of_nat (length (r_where rc)) + 8) [(bv_unsigned sp - 6032, bv_unsigned sp + -96); (DD, DD + 200)] ->
  evt rsegs Post (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp a1 t1 t2 a2 (Z_to_bv 64 (bv_unsigned a0 + 11912))
                       y10 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc)) * 200)) y12 (Z_to_bv 64 w) a4 a5 a6 a7
                       (Z_to_bv 64 (bv_unsigned a0 + 13512)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15d1c) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 j0 j1 P1 SL P3 NR R Q3 w y10 y12 t1 t2 t3 t4 t5 t6
    FR ST BP1 BSL B3 BN BRF BQ3 WC MU WM MI HE LP1 LSL LNR LR LQ3 ENR Hn8 Hw0 Hwr Hwc Hwa.
  nums.
  assert (HDD : DD = bv_unsigned a0 + 11912 + 200 * Z.of_nat (length (rc_refusal rc))) by reflexivity.
  pose proof (bytes_at_bound _ _ _ _ BQ3) as BBq. rewrite LQ3 in BBq.
  replace a1 with (Z_to_bv 64 ln) by (rewrite <- Hline; apply Z_to_bv_bv_unsigned).
  zstep.
  replace (bv_unsigned a0 + 11912 + Z.of_nat (length (rc_refusal rc)) * 200) with DD by (unfold DD; lia).
  zstep. lts_rw.
  destruct (Z.ltb_spec 0 ln) as [Hlt|Hle]; cbn [negb].
  - (* line > 0: "%s:%d: " *)
    do 6 zstep.
    eapply (snp_call true); [rewrite (proj2 (Z.ltb_lt 0 ln) Hlt); reflexivity | reflexivity | intros _; reflexivity
                            | exact FR | exact ST | exact BP1 | exact BSL | exact B3 | exact BN | exact BRF | exact BQ3
                            | exact WC | exact MU | exact WM | exact MI | exact HE | exact LP1 | exact LSL | exact LNR
                            | exact LR | exact LQ3 | exact ENR | exact Hn8 | exact Hw0 | exact Hwr | exact Hwc | exact Hwa].
  - (* line = 0: "%s: " *)
    do 5 zstep.
    eapply (snp_call false); [rewrite (proj2 (Z.ltb_ge 0 ln) Hle); reflexivity | reflexivity | intros Hf0; discriminate Hf0
                             | exact FR | exact ST | exact BP1 | exact BSL | exact B3 | exact BN | exact BRF | exact BQ3
                             | exact WC | exact MU | exact WM | exact MI | exact HE | exact LP1 | exact LSL | exact LNR
                             | exact LR | exact LQ3 | exact ENR | exact Hn8 | exact Hw0 | exact Hwr | exact Hwc | exact Hwa].
Qed.

Lemma walk : forall (t0 t1 t2 t3 t4 t5 t6 : word),
  evt rsegs Post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 REFUSE) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 t3 t4 t5 t6. unfold REFUSE.
  nums.
  pose proof (bytes_at_bound _ _ _ _ BC0) as BBc.
  pose proof (wr_at_block m _ _ BC0 ltac:(rewrite HLc; exact Hni)) as WC. rewrite HLc in WC.
  destruct (app_split bs0 (Z.to_nat 13516)) as (Q1 & T1 & EQ1 & LQ1); [lia|].
  subst bs0. rewrite length_app in HLc.
  destruct (app_split T1 4) as (R & Q3 & EQ2 & LR); [lia|]. subst T1.
  rewrite length_app in HLc.
  rewrite !length_app in BBc.
  apply bytes_at_app in BC0 as [BQ1 BT]. apply bytes_at_app in BT as [BR BQ3].
  rewrite LQ1 in BR, BQ3. rewrite LR in BQ3.
  assert (Enr : fld (Z.to_nat 13512) 4 Q1 = le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc))))).
  { unfold fldz, RC_NREF in Hnref. rewrite fld_app_l in Hnref by lia. exact Hnref. }
  assert (Erf : R = le4 (Z_to_bv 64 (rc_refused rc))).
  { unfold fldz, RC_REFUSED in Hrref. rewrite fld_app_r, fld_app_l, fld_full in Hrref by (rewrite ?length_app; lia).
    exact Hrref. }
  pose proof (munch_refl W2 m) as MU. unfold W2 in MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (proj1 ST0) as LO0.
  carve_frame 96%nat ST0.
  assert (LA0 : Z.land (bv_unsigned a0) 7 = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  do 8 zstep. rewrite ?LA0. do 4 zstep. zstep.
  let K := fresh "K" in if_cases K; [ first [ exfalso; zify_cond K; rewrite ?LA0 in K; lia | idtac ] .. ].
  do 4 zstep.
  assert (RD1 : ov_read_bytes rsegs m0 (wa (bv_unsigned a0 + 13516)) 4 = Some (le4 (Z_to_bv 64 (rc_refused rc)))).
  { rewrite <- Erf. replace (bv_unsigned a0 + 13516) with (bv_unsigned a0 + Z.of_nat (Z.to_nat 13516) + 0) by lia.
    rewrite (bytes_at_read rsegs m0 _ R 0 4 BR) by lia. change (skipn (Z.to_nat 0) R) with R. rewrite firstn_all2 by (rewrite LR; constructor). reflexivity. }
  assert (RD2 : ov_read_bytes rsegs m0 (wa (bv_unsigned a0 + 13512)) 4
                = Some (le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc)))))).
  { rewrite (bytes_at_read rsegs m0 _ Q1 13512 4 BQ1) by lia. rewrite <- Enr. reflexivity. }
  zstep. zstep. zstep. zstep.
  pose proof (wr_at_store_ok rsegs m0 (bv_unsigned a0) 16616 13516 4 WC ltac:(lia) ltac:(lia)) as SO.
  clear RD1 RD2 BR.
  step.
  pose proof (bytes_at_write_same rsegs m0 (bv_unsigned a0 + 13516)
                (le4 (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 (rc_refused rc))) + 1))) ltac:(lia)
                ltac:(rewrite length_le4; lia)) as BRF.
  rewrite (le4_inc (rc_refused rc)) in BRF |- * by lia.
  store_done.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  replace (bv_unsigned a0 + Z.of_nat (Z.to_nat 13516) + Z.of_nat 4) with (bv_unsigned a0 + 13520) in BQ3 by lia.
  rewrite (sx32_small (Z.of_nat (length (rc_refusal rc)))) by lia.
  zstep. lts_rw.
  destruct (Z.ltb_spec 7 (Z.of_nat (length (rc_refusal rc)))) as [Hn8|Hn8]; cbv iota.
  - (* n_refusals >= 8: refused++ only *)
    assert (Hn8' : (8 <= length (rc_refusal rc))%nat) by lia.
    apply (rw_cells_merge rsegs m1 _ [CB 16 _; C8 s2; C8 s1; C8 s0; C8 ra] [CB 8 _; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] [])
      in FR.
    cbn [app cells_size csize Nat.add] in FR.
    eapply epi; [exact FR | exact ST0 | exact MI0 | exact WM | exact MU | | | exact FRM | intros; reflexivity |].
    + unfold sub_fp, refuse_W, REFUSE_STACK, PRINTF_K, RC_REFUSED.
      rewrite (proj2 (Nat.ltb_ge _ _) Hn8'). cbn [outside app].
      intros x (H1 & H2 & _). split; [lia | split; [lia | exact I]].
    + intros x Hx. apply pres4. unfold W4. cbn [outside] in *. intros (H1 & H2 & H3 & H4 & _).
      apply Hx. split; [exact H1 | split; [exact H2 | exact I]].
    + unfold refuse. cbv zeta. rewrite (proj2 (Z.leb_le 8 (Z.of_nat (length (rc_refusal rc))))) by lia.
      exists (Q1 ++ le4 (Z_to_bv 64 (rc_refused rc + 1)) ++ Q3). split.
      * apply bytes_at_app. split; [exact BQ1|]. apply bytes_at_app. rewrite length_le4.
        replace (bv_unsigned a0 + Z.of_nat (length Q1)) with (bv_unsigned a0 + 13516) by lia.
        split; [exact BRF|].
        replace (bv_unsigned a0 + 13516 + Z.of_nat 4) with (bv_unsigned a0 + 13520) by lia.
        exact BQ3.
      * apply (enc_refd rc Q1 R Q3 HE0); [lia | exact LR | exact Hrf].
  - (* n_refusals < 8: the slot is written *)
    assert (Hn8' : (length (rc_refusal rc) < 8)%nat) by lia.
    assert (LQ3 : Z.of_nat (length Q3) = 3096) by lia.
    assert (Hrd96 : cstr_enc 96 (rc_reading rc) (fld 2992 96 Q3)).
    { pose proof HE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _). unfold fldz, RC_READING in Hrd.
      rewrite fld_app_r, fld_app_r in Hrd by (rewrite ?length_app; lia).
      replace (Z.to_nat 16512 - length Q1 - length R)%nat with 2992%nat in Hrd by lia.
      change (Z.to_nat 96) with 96%nat in Hrd. exact Hrd. }
    pose proof (reading_byte _ _ Hrd96) as Hb0.
    assert (RDb : ov_read_bytes rsegs m1 (wa (bv_unsigned a0 + 13520 + 2992)) 1 = Some [nth 0 (fld 2992 96 Q3) ZERO]).
    { rewrite (bytes_at_read rsegs m1 _ Q3 2992 1 BQ3) by lia. f_equal. change (Z.to_nat 2992) with 2992%nat.
      apply first_byte. lia. }
    set (b0 := nth 0 (fld 2992 96 Q3) ZERO) in *.
    pose proof (bytes_fld rsegs m1 _ Q3 2992 96 BQ3 ltac:(lia)) as BRD.
    replace (bv_unsigned a0 + 13520 + Z.of_nat 2992) with (bv_unsigned a0 + 16512) in BRD by lia.
    (* split c->seg .. c->refusal[n] | slot | the rest of refusal[] | n_refusals *)
    destruct (app_split Q1 (Z.to_nat (11912 + 200 * Z.of_nat (length (rc_refusal rc))))) as (P1 & T1 & EQa & LP1n);
      [lia|].
    subst Q1. rewrite length_app in LQ1.
    destruct (app_split T1 200) as (SL & T2 & EQb & LSL); [lia|]. subst T1. rewrite length_app in LQ1.
    destruct (app_split T2 (Z.to_nat (1400 - 200 * Z.of_nat (length (rc_refusal rc))))) as (P3 & NR & EQc & LP3n);
      [lia|].
    subst T2. rewrite length_app in LQ1.
    assert (LNR : length NR = 4%nat) by lia.
    apply bytes_at_app in BQ1 as [BP1 BT1]. apply bytes_at_app in BT1 as [BSL BT2]. apply bytes_at_app in BT2 as [B3 BN].
    replace (bv_unsigned a0 + Z.of_nat (length P1)) with DD in BSL by (unfold DD; lia).
    replace (bv_unsigned a0 + Z.of_nat (length P1)) with DD in B3 by (unfold DD; lia).
    replace (bv_unsigned a0 + Z.of_nat (length P1)) with DD in BN by (unfold DD; lia).
    replace (DD + Z.of_nat (length SL)) with (DD + 200) in B3 by lia.
    replace (DD + Z.of_nat (length SL)) with (DD + 200) in BN by lia.
    replace (DD + 200 + Z.of_nat (length P3)) with (bv_unsigned a0 + 13512) in BN by (unfold DD; lia).
    rewrite fld_app_r, fld_app_r, fld_app_r, fld_full in Enr by (rewrite ?length_app; lia).
    rewrite <- !app_assoc in HE0.
    assert (LP1 : Z.of_nat (length P1) = 11912 + 200 * Z.of_nat (length (rc_refusal rc))) by lia.
    zstep. zstep. ltu_rw. rewrite (proj2 (Z.ltb_lt (Z.of_nat (length (rc_refusal rc))) 9)) by lia. cbn [negb].
    do 6 zstep. zstep. rewrite zb_lxor_ones by lia. ltu_rw. ltb_false. cbv iota.
    do 4 zstep.
    zstep.
    unfold bv_eqb. rewrite (unsigned_lit (bv_unsigned b0))
      by (pose proof (bv_unsigned_in_range 8 b0) as Rb; change (bv_modulus 8) with 256 in Rb; lia).
    rewrite (unsigned_lit 0) by lia. rewrite Hb0.
    destruct (hd0 (rc_reading rc) =? 0) eqn:Hh; cbn [negb].
    + (* where = "reac-pw.conf" (.rodata 0x10463) *)
      assert (Ew : r_where rc = S_base) by (unfold r_where; rewrite Hh; reflexivity).
      zstep. zstep.
      eapply call1; [exact FR | exact ST0 | exact BP1 | exact BSL | exact B3 | exact BN | exact BRF | exact BQ3 | exact WC
                    | exact MU | exact WM | exact MI0 | exact HE0 | exact LP1 | exact LSL | exact LNR | exact LR | exact LQ3
                    | exact Enr | exact Hn8' | lia | lia | | ].
      * rewrite Ew. exact (sbase_at m1 MI0).
      * rewrite Ew. change (length S_base) with 12%nat.
        pose proof (noimg_disj _ _ 0x10000 0x3000 66659 20 DD 200 Hni
                      ltac:(unfold RES; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold DD; lia)
                      ltac:(unfold DD; lia) ltac:(lia)) as D1.
        apply apart_all2; unfold apart; lia.
    + (* where = c->reading *)
      assert (Ew : r_where rc = rc_reading rc) by (unfold r_where; rewrite Hh; reflexivity).
      pose proof reading_facts as (_ & HLr & _).
      eapply call1; [exact FR | exact ST0 | exact BP1 | exact BSL | exact B3 | exact BN | exact BRF | exact BQ3 | exact WC
                    | exact MU | exact WM | exact MI0 | exact HE0 | exact LP1 | exact LSL | exact LNR | exact LR | exact LQ3
                    | exact Enr | exact Hn8' | lia | lia | | ].
      * rewrite Ew. apply (cstr_of_enc rsegs m1 _ _ _ BRD Hrd96). Z.div_mod_to_equations. lia.
      * rewrite Ew. apply apart_all2; unfold apart, DD; lia.
Qed.

End W.

Theorem refuse_holds : rf_snprintf -> rf_vsnprintf -> refuse_contract.
Proof.
  intros HSN HVSN. unfold refuse_contract, refuse_pre.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ln rc f args
    (Hc0 & Hc16 & HRC & Hap & Himg & Hrf & Hln & Hline & Hf & Hck & Hfp0 & Hfz & Hro & Hfe & Hva & Henv & Hst & MI0).
  eapply walk; eassumption.
Qed.
