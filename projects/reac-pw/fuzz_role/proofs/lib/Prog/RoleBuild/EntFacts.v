(** Facts for the walk of rb_ent_contract (EntCut.v): the frame of one ent_build turn, its postcondition QJ for a
    given (e, r'), the memory MemC the walk carries (the contract's footprint so far, the input bytes, the four
    constant frame cells, e's 104 bytes), the transports of MemC across the turn's stores and calls, the joins of the
    cases at 0x134f0 .. 0x1350c, and the statements of the case entries (the jump table's targets and 0x13824).
    No function of the binary is proved here. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import EntCut.
Import ListNotations.
Open Scope Z_scope.

(** ** A function of one byte, checked on all 256 values *)
Lemma byte_of_unsigned : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma byte_check : forall (f g : byte -> Z),
  forallb (fun z => f (Z_to_bv 8 z) =? g (Z_to_bv 8 z)) (map Z.of_nat (seq 0 256)) = true -> forall b, f b = g b.
Proof.
  intros f g H b. rewrite forallb_forall in H. rewrite <- (byte_of_unsigned b). apply Z.eqb_eq. apply H.
  pose proof (byte_range b). apply in_map_iff. exists (Z.to_nat (bv_unsigned b)). split; [lia | apply in_seq; lia].
Qed.

Lemma byte_checkb : forall (f g : byte -> bool),
  forallb (fun z => Bool.eqb (f (Z_to_bv 8 z)) (g (Z_to_bv 8 z))) (map Z.of_nat (seq 0 256)) = true ->
  forall b, f b = g b.
Proof.
  intros f g H b. rewrite forallb_forall in H. rewrite <- (byte_of_unsigned b). apply Bool.eqb_prop. apply H.
  pose proof (byte_range b). apply in_map_iff. exists (Z.to_nat (bv_unsigned b)). split; [lia | apply in_seq; lia].
Qed.

(** [byte_eq] proves a goal [forall b : byte, L b = R b] (Z or bool) on all 256 bytes by computation. *)
Ltac byte_eq := first [apply byte_check | apply byte_checkb]; vm_compute; reflexivity.

Ltac simpl_len := rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app, ?length_zeros, ?repeat_length;
  cbn [length].

(** ** The frame: what the contract assumes at 0x132fc *)
Definition ent_pre (sp : word) (m : word -> option byte) (r : list byte) (src pp lo : Z) : Prop :=
  0 < src /\ bytes_at rsegs m src r /\ src + Z.of_nat (length r) <= lo /\
  bytes_at rsegs m (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 pp)) /\
  bytes_at rsegs m (bv_unsigned sp + 0x60) (le8 (Z_to_bv 64 (-0x4001))) /\
  bytes_at rsegs m (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 (-0x3ffd))) /\
  bytes_at rsegs m (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
  stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) /\ lo + MID_STACK <= bv_unsigned sp /\ bv_unsigned sp mod 16 = 0 /\
  (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) /\
  (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) /\
  mem_inv rsegs m.

(** The bytes the turn may change. *)
Definition WE (sp : word) : list (Z * Z) :=
  [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (bv_unsigned sp + 0x28, bv_unsigned sp + 0x30);
   (bv_unsigned sp + 0x78, bv_unsigned sp + 0x80); (bv_unsigned sp + 0x88, bv_unsigned sp + FRAME_LOCALS)].

(** The contract's postcondition, for the ent and the input left er. *)
Definition QJ (sp gp tp s7 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
    (src pp lo : Z) (er : ent * list byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t1' t2' a0' a1' a2' a3' a4' a5' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp (Z_to_bv 64 (-0x4001)) t1' t2' (Z_to_bv 64 (bv_unsigned sp + 0x128))
                  (Z_to_bv 64 (bv_unsigned sp + 0xf0)) a0' a1' a2' a3' a4' a5'
                  (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (-0x3ffd)) (Z_to_bv 64 (0xcccccccd * 2^32))
                  (Z_to_bv 64 (e_type (fst er))) (Z_to_bv 64 (e_size (fst er)))
                  (Z_to_bv 64 0x4000)
                  (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length (snd er))))
                  s7 (Z_to_bv 64 95) s9 (Z_to_bv 64 10) (Z_to_bv 64 pp) t3' t4' t5' t6')
             F (Z_to_bv 64 ENT_JOIN) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x78) (le8 (Z_to_bv 64 (Z.of_nat (length (snd er))))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x88) (ent_mem (fst er)) /\
    munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (bv_unsigned sp + 0x28, bv_unsigned sp + 0x30);
           (bv_unsigned sp + 0x78, bv_unsigned sp + 0x80); (bv_unsigned sp + 0x88, bv_unsigned sp + FRAME_LOCALS)]
          m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

(** The memory the walk carries: the footprint so far, the stack, the input, the constant cells, e's 104 bytes. *)
Definition MemC (sp : word) (m : word -> option byte) (r : list byte) (src pp lo : Z)
    (m1 : word -> option byte) (eb : list byte) : Prop :=
  munch (WE sp) m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
  stk rsegs m1 lo (bv_unsigned sp + FRAME_LOCALS) /\ bytes_at rsegs m1 src r /\
  rw_cells rsegs m1 (bv_unsigned sp + 80) [C8 (Z_to_bv 64 pp)] /\
  rw_cells rsegs m1 (bv_unsigned sp + 96) [C8 (Z_to_bv 64 (-0x4001))] /\
  rw_cells rsegs m1 (bv_unsigned sp + 104) [C8 (Z_to_bv 64 (-0x3ffd))] /\
  rw_cells rsegs m1 (bv_unsigned sp + 128) [C8 (Z_to_bv 64 (pp + POD_LEN_OFF))] /\
  bytes_at rsegs m1 (bv_unsigned sp + 136) eb /\ length eb = 104%nat.

(** ** General memory lemmas *)
Lemma stk_store_ok : forall m lo hi a (j : nat), stk rsegs m lo hi -> lo <= a -> a + Z.of_nat j <= hi ->
  store_ok rsegs m (wa a) j = true.
Proof.
  intros m lo hi a j (H1 & H2 & H) Ha Hj.
  assert (W : wr_at rsegs m lo (hi - lo)).
  { split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. }
  pose proof (wr_at_store_ok rsegs m lo (hi - lo) (a - lo) j W ltac:(lia) ltac:(lia)) as X.
  replace (lo + (a - lo)) with a in X by lia. exact X.
Qed.

Lemma stk_rw_cells : forall m lo hi A (n : nat), stk rsegs m lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  exists junk, length junk = n /\ rw_cells rsegs m A [CB n junk].
Proof.
  intros m lo hi A n Hs H1 H2. pose proof Hs as (S1 & S2 & S).
  assert (Hs' : stk rsegs m A (A + Z.of_nat n)).
  { split; [lia|]. split; [lia|]. intros a Ha. apply S. lia. }
  destruct (stk_bytes rsegs m A (A + Z.of_nat n) Hs' ltac:(lia)) as (bs & Hlen & Hb).
  replace (Z.to_nat (A + Z.of_nat n - A)) with n in Hlen by lia.
  exists bs. split; [exact Hlen|]. split.
  - split. { cbn. split; [lia | exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply S. lia.
Qed.

Lemma stk_bytes_at : forall m lo hi A (n : nat), stk rsegs m lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  exists bs, length bs = n /\ bytes_at rsegs m A bs.
Proof.
  intros m lo hi A n Hs H1 H2. destruct (stk_rw_cells m lo hi A n Hs H1 H2) as (bs & L & C).
  exists bs. split; [exact L|]. destruct C as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb.
  rewrite app_nil_r in Hb. exact Hb.
Qed.

(** The n bytes at A on the stack are writable cells holding what they hold. *)
Lemma stk_bytes_rw : forall m lo hi A bs, stk rsegs m lo hi -> bytes_at rsegs m A bs -> lo <= A ->
  A + Z.of_nat (length bs) <= hi -> rw_cells rsegs m A [CB (length bs) bs].
Proof.
  intros m lo hi A bs (S1 & S2 & S) Hb H1 H2. split.
  - split; [cbn; split; [reflexivity | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply S. lia.
Qed.

Lemma bytes_at_rw_C8 : forall m A (v : word) lo hi, bytes_at rsegs m A (le8 v) -> stk rsegs m lo hi ->
  lo <= A -> A + 8 <= hi -> rw_cells rsegs m A [C8 v].
Proof.
  intros m A v lo hi Hb (S1 & S2 & S) H1 H2. split.
  - split; [cbn; exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply S. lia.
Qed.

Lemma rw_CB_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[Hwf Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn in Hwf. destruct Hwf as [L _]. split; [exact Hb | exact L].
Qed.

Lemma bytes_at_munch_upd : forall m1 m2 c cs d (n : Z) bs,
  bytes_at rsegs m1 c cs -> munch [(d, d + n)] m1 m2 -> bytes_at rsegs m2 d bs -> Z.of_nat (length bs) = n ->
  c <= d -> d + n <= c + Z.of_nat (length cs) ->
  bytes_at rsegs m2 c (upd_bytes cs (Z.to_nat (d - c)) bs).
Proof.
  intros m1 m2 c cs d n bs (Hc0 & Hc1 & Hc) MU (Hd0 & Hd1 & Hd) Hn Hcd Hdn.
  unfold bytes_at. rewrite upd_bytes_length by lia. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite upd_bytes_nth by lia.
  destruct (Nat.leb (Z.to_nat (d - c)) i && Nat.ltb i (Z.to_nat (d - c) + length bs))%bool eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
    replace (c + Z.of_nat i) with (d + Z.of_nat (i - Z.to_nat (d - c))) by lia. apply Hd. lia.
  - unfold mrd. rewrite (MU (wa (c + Z.of_nat i))).
    + exact (Hc i Hi).
    + rewrite wa_unsigned by lia. cbn [outside]. split; [|exact I].
      apply andb_false_iff in E as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia.
Qed.

(** After a callee whose only writes are the n bytes at d, with those bytes present: the stack stays present. *)
Lemma stk_after_call : forall m1 m2 lo hi d (n : Z) bs,
  stk rsegs m1 lo hi -> munch [(d, d + n)] m1 m2 -> wmono rsegs m1 m2 -> bytes_at rsegs m2 d bs ->
  Z.of_nat (length bs) = n -> (forall a, lo <= a < hi -> seg_rom rsegs (wa a) = None) -> stk rsegs m2 lo hi.
Proof.
  intros m1 m2 lo hi d n bs Hs MU WM (B0 & B1 & B) Hn HR. pose proof Hs as (S1 & S2 & _).
  apply (stk_transport rsegs [(d, d + n)] m1 m2 lo hi Hs MU WM). intros x Hx.
  destruct (Z.le_gt_cases d x) as [H1|H1]; [destruct (Z.lt_ge_cases x (d + n)) as [H2|H2]|].
  - right. pose proof (B (Z.to_nat (x - d)) ltac:(lia)) as E. replace (d + Z.of_nat (Z.to_nat (x - d))) with x in E by lia.
    unfold mrd in E. rewrite (HR x Hx) in E. destruct (m2 (wa x)) as [b|]; [exists b; reflexivity|].
    destruct (nth_error bs (Z.to_nat (x - d))) eqn:N; [discriminate E|]. apply nth_error_None in N. lia.
  - left. cbn [outside]. split; [lia | exact I].
  - left. cbn [outside]. split; [lia | exact I].
Qed.

(** One byte, or eight, of a bytes_at run. *)
Lemma bytes_at_byte : forall m a bs j, bytes_at rsegs m a bs -> (j < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat j)) 1 = Some [nth j bs NUL].
Proof.
  intros m a bs j H Hj.
  rewrite (bytes_at_ov_read rsegs m a bs j 1 H) by lia.
  f_equal. clear H. revert j Hj. induction bs as [|x bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma bytes_at_read8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H L. pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. cbn [skipn]. f_equal. rewrite <- L. apply firstn_all.
Qed.

Lemma upd_bytes_all : forall (cs bs : list byte), length bs = length cs -> upd_bytes cs 0 bs = bs.
Proof.
  intros cs bs H. unfold upd_bytes. cbn [firstn]. rewrite Nat.add_0_l, H, skipn_all, app_nil_r. reflexivity.
Qed.

(** The n bytes from k of a run. *)
Lemma bytes_at_sub : forall m a l k n, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H2].
  rewrite length_firstn in H2. replace (Nat.min k (length l)) with k in H2 by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in H2. apply bytes_at_app in H2 as [H3 _]. exact H3.
Qed.

(** Bytes of the image's read-only segments at A, in any memory with mem_inv. *)
Lemma image_bytes_at : forall m A bs, mem_inv rsegs m -> ro_bytes_b rsegs A bs = true -> 0 <= A ->
  A + Z.of_nat (length bs) <= 2^64 -> bytes_at rsegs m A bs.
Proof.
  intros m A bs MI H H0 H1. pose proof (ro_cells_image rsegs m A bs MI H H0 H1) as [_ B].
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

(** Every byte of a range present in the image (checked by computation). *)
Definition rom_some (a : Z) : bool := match seg_rom rsegs (wa a) with Some _ => true | None => false end.

Lemma rom_range : forall base n, forallb (fun j => rom_some (base + Z.of_nat j)) (seq 0 n) = true ->
  forall a, base <= a < base + Z.of_nat n -> seg_rom rsegs (wa a) <> None.
Proof.
  intros base n H a Ha. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - base)) ltac:(apply in_seq; lia)). unfold rom_some in H.
  replace (base + Z.of_nat (Z.to_nat (a - base))) with a in H by lia.
  destruct (seg_rom rsegs (wa a)); [discriminate | discriminate H].
Qed.

(** Carry the bytes_at facts on m1 across a store of bs at a (dropping the ones the store overlaps). *)
Ltac carry_bytes m1 a bs :=
  repeat match goal with
  | H : bytes_at rsegs m1 ?A ?cs |- _ =>
      first [ apply (bytes_at_write_other rsegs m1 a bs A cs) in H;
              [ cbv delta [wa] in H | lia | simpl_len; lia | simpl_len; lia ]
            | idtac "note: dropping" H; clear H ]
  end.

(** ** The walk's frame *)
Section Frame.
Variables (sp : word) (m : word -> option byte) (r : list byte) (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Lemma ep_src : 0 < src /\ src + Z.of_nat (length r) <= lo /\ bytes_at rsegs m src r.
Proof. destruct HE as (H1 & H2 & H3 & _). tauto. Qed.

Lemma ep_stk : stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) /\ lo + MID_STACK <= bv_unsigned sp /\
  bv_unsigned sp mod 16 = 0 /\ 0 <= lo /\ bv_unsigned sp + FRAME_LOCALS <= 2^64.
Proof. destruct HE as (_ & _ & _ & _ & _ & _ & _ & H & H1 & H2 & _). pose proof H as (A & B & _). tauto. Qed.

Lemma ep_rom : forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None.
Proof. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma ep_relro : forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).
Proof. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

(** The address facts every lia below needs. *)
Lemma ep_range : 0 < src /\ src + Z.of_nat (length r) <= lo /\ 0 <= lo /\ lo + 96 <= bv_unsigned sp /\
  bv_unsigned sp + 0x188 <= 2^64 /\ bv_unsigned sp mod 16 = 0.
Proof.
  pose proof ep_src as (A & B & _). pose proof ep_stk as (_ & C & D & E & G).
  unfold MID_STACK, FRAME_LOCALS in *. lia.
Qed.

(** A range of the image is apart from the stack region [lo, sp + 0x188). *)
Lemma img_apart : forall A (n : nat), forallb (fun j => rom_some (A + Z.of_nat j)) (seq 0 n) = true -> (0 < n)%nat ->
  A + Z.of_nat n <= lo \/ bv_unsigned sp + FRAME_LOCALS <= A.
Proof.
  intros A n H Hn. pose proof (rom_range A n H) as RR. pose proof ep_range as R.
  destruct (Z.le_gt_cases (A + Z.of_nat n) lo) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases (bv_unsigned sp + FRAME_LOCALS) A) as [|H2]; [right; lia|].
  exfalso. apply (RR (Z.max A lo)); [lia|]. apply ep_rom. unfold FRAME_LOCALS in *. lia.
Qed.

(** The memory at 0x132fc. *)
Lemma MemC_init : exists eb, MemC sp m r src pp lo m eb.
Proof.
  pose proof ep_range as R. pose proof ep_stk as (ST & _).
  destruct (stk_bytes_at m lo (bv_unsigned sp + FRAME_LOCALS) (bv_unsigned sp + 136) 104 ST) as (eb & L & B);
    [unfold FRAME_LOCALS; lia | unfold FRAME_LOCALS; lia |].
  exists eb.
  destruct HE as (_ & HR & _ & H50 & H60 & H68 & H80 & _ & _ & _ & _ & _ & MI).
  unfold MemC. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
  split; [exact HR|].
  split; [apply (bytes_at_rw_C8 m _ _ lo (bv_unsigned sp + FRAME_LOCALS)); [exact H50 | exact ST | | ]; unfold FRAME_LOCALS; lia|].
  split; [apply (bytes_at_rw_C8 m _ _ lo (bv_unsigned sp + FRAME_LOCALS)); [exact H60 | exact ST | | ]; unfold FRAME_LOCALS; lia|].
  split; [apply (bytes_at_rw_C8 m _ _ lo (bv_unsigned sp + FRAME_LOCALS)); [exact H68 | exact ST | | ]; unfold FRAME_LOCALS; lia|].
  split; [apply (bytes_at_rw_C8 m _ _ lo (bv_unsigned sp + FRAME_LOCALS)); [exact H80 | exact ST | | ]; unfold FRAME_LOCALS; lia|].
  split; [exact B | exact L].
Qed.

(** A store of bs at a inside the footprint, apart from e and the four constant cells. *)
Lemma MemC_store_out : forall m1 eb a bs, MemC sp m r src pp lo m1 eb ->
  (bv_unsigned sp + 0x28 <= a /\ a + Z.of_nat (length bs) <= bv_unsigned sp + 0x30 \/
   bv_unsigned sp + 0x78 <= a /\ a + Z.of_nat (length bs) <= bv_unsigned sp + 0x80 \/
   bv_unsigned sp + 0xf0 <= a /\ a + Z.of_nat (length bs) <= bv_unsigned sp + FRAME_LOCALS) ->
  MemC sp m r src pp lo (write_to_mem m1 (Z_to_bv 64 a) bs) eb.
Proof.
  intros m1 eb a bs (MU & WM & MI & ST & HR & C50 & C60 & C68 & C80 & EB & L) Hin.
  pose proof ep_range as R. pose proof ST as (S1 & S2 & _). unfold FRAME_LOCALS in *.
  assert (HS : store_ok rsegs m1 (wa a) (length bs) = true)
    by (apply (stk_store_ok m1 lo (bv_unsigned sp + FRAME_LOCALS)); [exact ST | | unfold FRAME_LOCALS]; lia).
  change (Z_to_bv 64 a) with (wa a).
  unfold MemC. split.
  { apply munch_write; [exact MU | lia | lia |]. unfold WE, FRAME_LOCALS. cbn [inside]. lia. }
  split; [apply wmono_write; exact WM|]. split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply stk_write; [exact ST | lia | lia]|].
  split; [apply bytes_at_write_other; [exact HR | lia | lia | lia]|].
  split; [apply rw_cells_frame; [exact C50 | lia | lia | cbn; lia]|].
  split; [apply rw_cells_frame; [exact C60 | lia | lia | cbn; lia]|].
  split; [apply rw_cells_frame; [exact C68 | lia | lia | cbn; lia]|].
  split; [apply rw_cells_frame; [exact C80 | lia | lia | cbn; lia]|].
  split; [apply bytes_at_write_other; [exact EB | lia | lia | lia] | exact L].
Qed.

(** A store of bs at e + k. *)
Lemma MemC_store_e : forall m1 eb a k bs, MemC sp m r src pp lo m1 eb ->
  a = bv_unsigned sp + 136 + k -> 0 <= k -> k + Z.of_nat (length bs) <= 104 ->
  MemC sp m r src pp lo (write_to_mem m1 (Z_to_bv 64 a) bs) (upd_bytes eb (Z.to_nat k) bs).
Proof.
  intros m1 eb a k bs (MU & WM & MI & ST & HR & C50 & C60 & C68 & C80 & EB & L) -> Hk Hkb.
  pose proof ep_range as R. pose proof ST as (S1 & S2 & _).
  assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + 136 + k)) (length bs) = true)
    by (apply (stk_store_ok m1 lo (bv_unsigned sp + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  change (Z_to_bv 64 (bv_unsigned sp + 136 + k)) with (wa (bv_unsigned sp + 136 + k)).
  unfold MemC. split.
  { apply munch_write; [exact MU | lia | lia |]. unfold WE. cbn [inside]. unfold FRAME_LOCALS. lia. }
  split; [apply wmono_write; exact WM|]. split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply stk_write; [exact ST | lia | lia]|].
  split; [apply bytes_at_write_other; [exact HR | lia | lia | lia]|].
  split; [apply rw_cells_frame; [exact C50 | lia | lia | cbn; lia]|].
  split; [apply rw_cells_frame; [exact C60 | lia | lia | cbn; lia]|].
  split; [apply rw_cells_frame; [exact C68 | lia | lia | cbn; lia]|].
  split; [apply rw_cells_frame; [exact C80 | lia | lia | cbn; lia]|].
  split; [apply bytes_at_write_inside; [exact EB | lia | lia] | rewrite upd_bytes_length; lia].
Qed.

(** A callee that writes the n bytes bs at d inside e. *)
Lemma MemC_call_e : forall m1 m2 eb d (n : Z) bs, MemC sp m r src pp lo m1 eb ->
  munch [(d, d + n)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> bytes_at rsegs m2 d bs ->
  Z.of_nat (length bs) = n -> bv_unsigned sp + 136 <= d -> d + n <= bv_unsigned sp + 240 ->
  MemC sp m r src pp lo m2 (upd_bytes eb (Z.to_nat (d - (bv_unsigned sp + 136))) bs).
Proof.
  intros m1 m2 eb d n bs (MU & WM & MI & ST & HR & C50 & C60 & C68 & C80 & EB & L) MU2 WM2 MI2 B2 Hn H1 H2.
  pose proof ep_range as R.
  unfold MemC. split.
  { apply (munch_trans _ m m1 m2 MU). apply (munch_weaken [(d, d + n)] _ m1 m2); [|exact MU2].
    unfold sub_fp, WE. cbn [outside]. unfold FRAME_LOCALS. intros x (O1 & O2 & O3 & O4 & _). split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|]. split; [exact MI2|].
  split; [apply (stk_after_call m1 m2 lo _ d n bs ST MU2 WM2 B2 Hn); exact ep_rom|].
  split; [apply (bytes_at_transport rsegs _ m1 m2 _ _ HR MU2); cbn [disjoint_from]; split; [lia | exact I]|].
  split; [apply (rw_cells_transport rsegs _ m1 m2 _ _ C50 MU2 WM2); cbn [disjoint_from cells_size csize]; split; [lia | exact I]|].
  split; [apply (rw_cells_transport rsegs _ m1 m2 _ _ C60 MU2 WM2); cbn [disjoint_from cells_size csize]; split; [lia | exact I]|].
  split; [apply (rw_cells_transport rsegs _ m1 m2 _ _ C68 MU2 WM2); cbn [disjoint_from cells_size csize]; split; [lia | exact I]|].
  split; [apply (rw_cells_transport rsegs _ m1 m2 _ _ C80 MU2 WM2); cbn [disjoint_from cells_size csize]; split; [lia | exact I]|].
  split; [apply (bytes_at_munch_upd m1 m2 _ eb d n bs EB MU2 B2 Hn); lia | rewrite upd_bytes_length; lia].
Qed.

(** A callee that writes the n bytes bs at d in [sp + 0xf0, sp + 0x188), apart from e. *)
Lemma MemC_call_hi : forall m1 m2 eb d (n : Z) bs, MemC sp m r src pp lo m1 eb ->
  munch [(d, d + n)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> bytes_at rsegs m2 d bs ->
  Z.of_nat (length bs) = n -> bv_unsigned sp + 240 <= d -> d + n <= bv_unsigned sp + FRAME_LOCALS ->
  MemC sp m r src pp lo m2 eb.
Proof.
  intros m1 m2 eb d n bs (MU & WM & MI & ST & HR & C50 & C60 & C68 & C80 & EB & L) MU2 WM2 MI2 B2 Hn H1 H2.
  pose proof ep_range as R. unfold FRAME_LOCALS in *.
  unfold MemC. split.
  { apply (munch_trans _ m m1 m2 MU). apply (munch_weaken [(d, d + n)] _ m1 m2); [|exact MU2].
    unfold sub_fp, WE. cbn [outside]. unfold FRAME_LOCALS. intros x (O1 & O2 & O3 & O4 & _). split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|]. split; [exact MI2|].
  split; [apply (stk_after_call m1 m2 lo _ d n bs ST MU2 WM2 B2 Hn); exact ep_rom|].
  split; [apply (bytes_at_transport rsegs _ m1 m2 _ _ HR MU2); cbn [disjoint_from]; split; [lia | exact I]|].
  split; [apply (rw_cells_transport rsegs _ m1 m2 _ _ C50 MU2 WM2); cbn [disjoint_from cells_size csize]; split; [lia | exact I]|].
  split; [apply (rw_cells_transport rsegs _ m1 m2 _ _ C60 MU2 WM2); cbn [disjoint_from cells_size csize]; split; [lia | exact I]|].
  split; [apply (rw_cells_transport rsegs _ m1 m2 _ _ C68 MU2 WM2); cbn [disjoint_from cells_size csize]; split; [lia | exact I]|].
  split; [apply (rw_cells_transport rsegs _ m1 m2 _ _ C80 MU2 WM2); cbn [disjoint_from cells_size csize]; split; [lia | exact I]|].
  split; [|exact L].
  apply (bytes_at_transport rsegs _ m1 m2 _ _ EB MU2). cbn [disjoint_from]. rewrite L. split; [lia | exact I].
Qed.

(** A callee that writes nothing (strlen). *)
Lemma MemC_call_nil : forall m1 m2 eb, MemC sp m r src pp lo m1 eb ->
  munch [] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> MemC sp m r src pp lo m2 eb.
Proof.
  intros m1 m2 eb (MU & WM & MI & ST & HR & C50 & C60 & C68 & C80 & EB & L) MU2 WM2 MI2.
  unfold MemC. split; [apply (munch_trans _ m m1 m2 MU); exact (munch_weaken [] _ m1 m2 (fun x _ => I) MU2)|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|]. split; [exact MI2|].
  split; [exact (stk_transport_disjoint rsegs _ _ _ _ _ ST MU2 WM2 I)|].
  split; [exact (bytes_at_transport rsegs _ _ _ _ _ HR MU2 I)|].
  split; [exact (rw_cells_transport rsegs _ _ _ _ _ C50 MU2 WM2 I)|].
  split; [exact (rw_cells_transport rsegs _ _ _ _ _ C60 MU2 WM2 I)|].
  split; [exact (rw_cells_transport rsegs _ _ _ _ _ C68 MU2 WM2 I)|].
  split; [exact (rw_cells_transport rsegs _ _ _ _ _ C80 MU2 WM2 I)|].
  split; [exact (bytes_at_transport rsegs _ _ _ _ _ EB MU2 I) | exact L].
Qed.

(** The input byte k. *)
Lemma MemC_in_byte : forall m1 eb (k : nat), MemC sp m r src pp lo m1 eb -> (k < length r)%nat ->
  ov_read_bytes rsegs m1 (wa (src + Z.of_nat k)) 1 = Some [nth k r NUL].
Proof. intros m1 eb k (_ & _ & _ & _ & HR & _) Hk. apply bytes_at_byte; assumption. Qed.

Lemma MemC_in : forall m1 eb, MemC sp m r src pp lo m1 eb -> bytes_at rsegs m1 src r.
Proof. intros m1 eb (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma MemC_mem_inv : forall m1 eb, MemC sp m r src pp lo m1 eb -> mem_inv rsegs m1.
Proof. intros m1 eb (_ & _ & H & _). exact H. Qed.

Lemma MemC_stk : forall m1 eb, MemC sp m r src pp lo m1 eb -> stk rsegs m1 lo (bv_unsigned sp + FRAME_LOCALS).
Proof. intros m1 eb (_ & _ & _ & H & _). exact H. Qed.

Lemma MemC_e : forall m1 eb, MemC sp m r src pp lo m1 eb -> bytes_at rsegs m1 (bv_unsigned sp + 136) eb.
Proof. intros m1 eb (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma MemC_len : forall m1 eb, MemC sp m r src pp lo m1 eb -> length eb = 104%nat.
Proof. intros m1 eb (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma MemC_e_ext : forall m1 eb eb', MemC sp m r src pp lo m1 eb -> eb = eb' -> MemC sp m r src pp lo m1 eb'.
Proof. intros; subst; assumption. Qed.

(** n writable bytes at a on the stack (a callee's destination). *)
Lemma MemC_cells : forall m1 eb a (n : nat), MemC sp m r src pp lo m1 eb ->
  bv_unsigned sp + 0x88 <= a -> a + Z.of_nat n <= bv_unsigned sp + FRAME_LOCALS ->
  exists junk, length junk = n /\ rw_cells rsegs m1 a [CB n junk].
Proof.
  intros m1 eb a n MC H1 H2. pose proof ep_range as R.
  apply (stk_rw_cells m1 lo (bv_unsigned sp + FRAME_LOCALS) a n (MemC_stk m1 eb MC)); lia.
Qed.

(** The .data.rel.ro tables read as in the image. *)
Lemma MemC_relro : forall m1 eb a, MemC sp m r src pp lo m1 eb -> RELRO_TBL <= a < RELRO_TBL_END ->
  seg_rom rsegs (wa a) <> None -> mrd rsegs m1 (wa a) = seg_rom rsegs (wa a).
Proof.
  intros m1 eb a (MU & _) Ha Hr. pose proof ep_range as R.
  assert (N : ~ (lo <= a < bv_unsigned sp + FRAME_LOCALS)) by (intros X; exact (Hr (ep_rom a X))).
  assert (Ho : outside (WE sp) a).
  { unfold WE. cbn [outside]. unfold MID_STACK, FRAME_LOCALS in *. repeat split; try exact I; lia. }
  unfold mrd. rewrite (MU (wa a)); [exact (ep_relro a Ha)|].
  rewrite wa_unsigned by (unfold RELRO_TBL, RELRO_TBL_END in *; lia). exact Ho.
Qed.

End Frame.

(** After a store step whose memory is [write_to_mem m1 (Z_to_bv 64 a) bs]: carry MemC (into e at offset k, or
    elsewhere in the footprint) and the other bytes_at facts on m1, and name the new memory. *)
Ltac mstore_e HE k :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 (Z_to_bv 64 ?a) ?bs) _) =>
    lazymatch goal with
    | MC : MemC _ _ _ _ _ _ m1 ?eb |- _ =>
      let MC2 := fresh "MC" in
      pose proof (MemC_store_e _ _ _ _ _ _ HE m1 eb a k bs MC ltac:(lia) ltac:(lia) ltac:(simpl_len; lia)) as MC2;
      clear MC; carry_bytes m1 a bs;
      repeat match goal with H : store_ok _ m1 _ _ = true |- _ => clear H end;
      let m2 := fresh "m" in let Em := fresh "Em" in
      remember (write_to_mem m1 (Z_to_bv 64 a) bs) as m2 eqn:Em; clear Em; try clear m1
    end
  end.

Ltac mstore_out HE :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 (Z_to_bv 64 ?a) ?bs) _) =>
    lazymatch goal with
    | MC : MemC _ _ _ _ _ _ m1 ?eb |- _ =>
      let MC2 := fresh "MC" in let HW := fresh "HW" in
      pose proof (MemC_store_out _ _ _ _ _ _ HE m1 eb a bs MC ltac:(simpl_len; unfold FRAME_LOCALS; lia)) as MC2;
      clear MC; carry_bytes m1 a bs;
      repeat match goal with H : store_ok _ m1 _ _ = true |- _ => clear H end;
      assert (HW : bytes_at rsegs (write_to_mem m1 (Z_to_bv 64 a) bs) a bs)
        by (apply bytes_at_write_same; simpl_len; lia);
      let m2 := fresh "m" in let Em := fresh "Em" in
      remember (write_to_mem m1 (Z_to_bv 64 a) bs) as m2 eqn:Em; clear Em; try clear m1
    end
  end.

(** The store_ok a store step of n bytes at a needs, from MemC's stack. *)
Ltac pre_store HE a n :=
  lazymatch goal with
  | MC : MemC _ _ _ _ _ _ ?m1 _ |- _ =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m1 (wa a) n = true)
      by (apply (stk_store_ok m1 _ _ _ n (MemC_stk _ _ _ _ _ _ _ _ MC)); unfold FRAME_LOCALS; lia)
  end.

(** The four constant cells of the current MemC, for the loads (stale ones dropped). *)
Ltac mcells :=
  repeat match goal with H : rw_cells rsegs _ _ [C8 _] |- _ => clear H end;
  lazymatch goal with
  | MC : MemC _ _ _ _ _ _ _ _ |- _ =>
    let C50 := fresh "C50" in let C60 := fresh "C60" in let C68 := fresh "C68" in let C80 := fresh "C80" in
    pose proof MC as (_ & _ & _ & _ & _ & C50 & C60 & C68 & C80 & _)
  end.

(** The mem_inv of the current MemC, for the image loads. *)
Ltac mmi :=
  repeat match goal with H : mem_inv rsegs _ |- _ => clear H end;
  lazymatch goal with
  | MC : MemC _ _ _ _ _ _ _ _ |- _ => let MI := fresh "MI" in pose proof MC as (_ & _ & MI & _)
  end.

(** A 32-bit store's bytes. *)
Lemma le4_any : forall w, le4 (Z_to_bv 64 w) = le32 w.
Proof.
  intros w. unfold le4, le32. rewrite Z_to_bv_unsigned. change (bv_wrap 64 w) with (w mod 2^64).
  apply Z_to_le_bytes_mod. cbn. lia.
Qed.

(** ** The joins of the cases *)
Section Join.
Variables (sp gp tp s7 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Local Abbreviation QE := (QJ sp gp tp s7 s9 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 (bv_unsigned sp + 0x128)).
Local Abbreviation S1 := (Z_to_bv 64 (bv_unsigned sp + 0xf0)).
Local Abbreviation S2 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S8 := (Z_to_bv 64 95).
Local Abbreviation S10 := (Z_to_bv 64 10).

(** 0x1350c, the end of the turn. *)
Lemma join_1350c : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1 e r',
  ent_build r = (e, r') ->
  t0 = Z_to_bv 64 (-0x4001) -> a6 = Z_to_bv 64 (pp + POD_LEN_OFF) -> a7 = Z_to_bv 64 (-0x3ffd) ->
  s3 = Z_to_bv 64 (e_type e) -> s4 = Z_to_bv 64 (e_size e) -> s5 = Z_to_bv 64 0x4000 ->
  s6 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) -> s11 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (ent_mem e) ->
  bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1350c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 e r' Eb -> -> -> -> -> -> -> ->
    (MU & WM & MI & ST & _ & _ & _ & _ & _ & EB & _) H78.
  apply evt_done. unfold QJ. rewrite Eb. cbn [fst snd].
  exists ra, t1, t2, a0, a1, a2, a3, a4, a5, t3, t4, t5, t6, m1.
  split; [reflexivity|]. split; [exact H78|]. split; [exact EB|]. split; [exact MU|].
  split; [exact WM|]. split; [exact MI | exact ST].
Qed.

(** 0x13504 `ld a7,0x68(sp); ld t0,0x60(sp)`. *)
Lemma join_13504 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1 e r',
  ent_build r = (e, r') -> a6 = Z_to_bv 64 (pp + POD_LEN_OFF) ->
  s3 = Z_to_bv 64 (e_type e) -> s4 = Z_to_bv 64 (e_size e) -> s5 = Z_to_bv 64 0x4000 ->
  s6 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) -> s11 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (ent_mem e) ->
  bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13504) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 e r' Eb E6 E3 E4 E5 E66 E11 MC H78.
  pose proof MC as (_ & _ & _ & _ & _ & C50 & C60 & C68 & C80 & _).
  step. step.
  eapply join_1350c; eauto.
Qed.

(** 0x134fc `ld a6,0x80(sp); lui s5,0x4`. *)
Lemma join_134fc : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1 e r',
  ent_build r = (e, r') ->
  s3 = Z_to_bv 64 (e_type e) -> s4 = Z_to_bv 64 (e_size e) ->
  s6 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) -> s11 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (ent_mem e) ->
  bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134fc) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 e r' Eb E3 E4 E66 E11 MC H78.
  pose proof MC as (_ & _ & _ & _ & _ & C50 & C60 & C68 & C80 & _).
  step. step.
  eapply join_13504; eauto.
Qed.

(** 0x134f8 `ld s11,0x50(sp)`. *)
Lemma join_134f8 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1 e r',
  ent_build r = (e, r') ->
  s3 = Z_to_bv 64 (e_type e) -> s4 = Z_to_bv 64 (e_size e) ->
  s6 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  MemC sp m r src pp lo m1 (ent_mem e) ->
  bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134f8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 e r' Eb E3 E4 E66 MC H78.
  pose proof MC as (_ & _ & _ & _ & _ & C50 & C60 & C68 & C80 & _).
  step.
  eapply join_134fc; eauto.
Qed.

Lemma le4_type : forall t, 0 <= t < 2^32 -> le4 (Z_to_bv 64 t) = le32 t.
Proof. intros t Ht. unfold le4, le32. rewrite unsigned_lit by lia. reflexivity. Qed.

(** e's bytes when its type and size are put last (0x134f0): eight bytes, the body, zeros. *)
Lemma ent_mem_put : forall e (h : list byte), length h = 8%nat -> 0 <= e_type e < 2^32 -> 0 <= e_size e < 2^32 ->
  upd_bytes (upd_bytes (h ++ e_body e ++ zeros (96 - length (e_body e))) 0 (le4 (Z_to_bv 64 (e_type e))))
            4 (le4 (Z_to_bv 64 (e_size e)))
  = ent_mem e.
Proof.
  intros e h Hh Ht Hs. rewrite !le4_type by lia. unfold ent_mem, upd_bytes.
  destruct h as [|h0 [|h1 [|h2 [|h3 [|h4 [|h5 [|h6 [|h7 [|]]]]]]]]]; cbn in Hh; try lia.
  reflexivity.
Qed.

(** 0x134f0 `sw s3,0x88(sp); sw s4,0x8c(sp)`. *)
Lemma join_134f0 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1 e r' h,
  ent_build r = (e, r') -> length h = 8%nat ->
  0 <= e_type e < 2^32 -> 0 <= e_size e < 2^32 ->
  s3 = Z_to_bv 64 (e_type e) -> s4 = Z_to_bv 64 (e_size e) ->
  s6 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  MemC sp m r src pp lo m1 (h ++ e_body e ++ zeros (96 - length (e_body e))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134f0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 e r' h Eb Hh Ht Hs E3 E4 E66 MC H78.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pre_store HE (bv_unsigned sp + 136) 4%nat. step. mstore_e HE 0.
  pre_store HE (bv_unsigned sp + 140) 4%nat. step. mstore_e HE 4.
  eapply join_134f8; [exact Eb | exact E3 | exact E4 | exact E66 | | exact H78].
  eapply MemC_e_ext; [eassumption|]. subst s3 s4. apply ent_mem_put; assumption.
Qed.

End Join.

(** ** The case entries *)
(** At a target of the jump table (cases 0-8: kind = b, kind % 10 = k) or at 0x13824 (case 9), after memset(e) and
    the kind read: a5 = src + 1, s4 = |r|, s5 = |r| - 1, s6 = src, e zero; s11 = (int8) kind (its sign is kind's bit
    7) at a table target, s11 = pp at 0x13824 (the branch to it is before 0x13358). *)
Definition case_at (sp gp tp s7 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
    (src pp lo : Z) (k pc : Z) : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) (b : byte) (rest : list byte) m1,
    r = b :: rest -> bv_unsigned b mod 10 = k ->
    (bv_signed s11 < 0 <-> Z.testbit (bv_unsigned b) 7 = true) ->
    a5 = Z_to_bv 64 (src + 1) -> s4 = Z_to_bv 64 (Z.of_nat (length r)) ->
    s5 = Z_to_bv 64 (Z.of_nat (length r) - 1) -> s6 = Z_to_bv 64 src ->
    MemC sp m r src pp lo m1 (zeros 104) ->
    evt rsegs (QJ sp gp tp s7 s9 F fc m r src pp lo (ent_build r))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (0xcccccccd * 2^32)) s3 s4 s5 s6 s7 (Z_to_bv 64 95) s9
               (Z_to_bv 64 10) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

Definition case9_at (sp gp tp s7 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
    (src pp lo : Z) : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) (b : byte) (rest : list byte) m1,
    r = b :: rest -> bv_unsigned b mod 10 = 9 ->
    a5 = Z_to_bv 64 (src + 1) -> s4 = Z_to_bv 64 (Z.of_nat (length r)) ->
    s5 = Z_to_bv 64 (Z.of_nat (length r) - 1) -> s6 = Z_to_bv 64 src -> s11 = Z_to_bv 64 pp ->
    MemC sp m r src pp lo m1 (zeros 104) ->
    evt rsegs (QJ sp gp tp s7 s9 F fc m r src pp lo (ent_build r))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (0xcccccccd * 2^32)) s3 s4 s5 s6 s7 (Z_to_bv 64 95) s9
               (Z_to_bv 64 10) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13824) fc None m1 (seg_rom rsegs)).

(** The input empty (0x1337c, kind = 0 read from nothing): case 0's head-amp key of no bytes. *)
Definition case0_nil_at (sp gp tp s7 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z) : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1,
    r = [] -> s4 = Z_to_bv 64 0 -> s6 = Z_to_bv 64 src ->
    MemC sp m r src pp lo m1 (zeros 104) ->
    evt rsegs (QJ sp gp tp s7 s9 F fc m r src pp lo (ent_build r))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (0xcccccccd * 2^32)) s3 s4 s5 s6 s7 (Z_to_bv 64 95) s9
               (Z_to_bv 64 10) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1337c) fc None m1 (seg_rom rsegs)).
