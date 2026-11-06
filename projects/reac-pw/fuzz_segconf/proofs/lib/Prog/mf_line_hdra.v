(** m_file (plain build, image 3776ca44d75c, 0x13fb4): the sub-piece S_MF_HDRA of the walk of S_MF_LINE
    (Prog/mf_cuts.v, family F3). From the cut HDR 0x14188 (m_header inline, fuzz_segconf.c:159-176) to the cut
    HFIND 0x14488, or through a refusal (m_refuse at 0x14644 or 0x144c8, cur = NULL) to the tail 0x143d4.

    Code (the plain build's disassembly):
      0x14188-0x14190  memchr(s5 = s, ']', a2 = e - s); 0x14194 none -> 0x1463c; s4 = close; 0x141a0
                       close + 1 <> e -> 0x1463c
      0x141a4-0x141fc  strip of [s + 1, close): forward 0x141b4 (s6), backward 0x141d8 (s4); both end at 0x143e4
                       with s5 = 9 (0x143e0 / 0x141f4), s6 = b, s4 = be
      0x143e4-0x143ec  s7 = be - b; be - b < 8 -> 0x144c0
      0x143f0-0x14400  ieq(b, 7, "segment" 0x10313); 0 -> 0x144c0; 0x14408 b[7] neither '\t' (s5) nor ' ' (s11)
                       -> 0x144c0
      0x14414-0x14474  strip of [b + 7, be): forward 0x14424 (s5, the count s7), s7 = 9 at 0x14448, backward
                       0x14458 (s4, a1; a0 = s5)
      0x14478-0x14484  empty name or 16 bytes or more -> 0x1463c; else HFIND 0x14488 (s5 = name, s6 = length)
      0x1463c-0x1464c  m_refuse(c, line + 1), `sd zero, 0x20(sp)`, j 0x143d4
      0x144c0-0x144d0  m_refuse(c, line + 1), `sd zero, 0x20(sp)`, j 0x14598 (s7 = 9), j 0x143d4
    The model side: mfp_facts.m_header_find (all checks pass: the step is mh_find of the name) and
    m_header_refuse (any check fails). The strip loops are SegModel.h_strip by mfp_facts.h_strip_idx; one lemma
    per loop shape (ha_f1 / ha_b1 forward and backward of the first strip, ha_f2 / ha_b2 of the second). *)
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrFun SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c mf_cuts
  mfu_facts mfp_facts mfp_mconf mf_common memchr_c ieq_c m_refuse_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Bytes, lists and the blank test *)
Lemma ha_u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. lia.
Qed.

Lemma ha_zs_inj : forall l l' : list byte, zs l = zs l' -> l = l'.
Proof.
  unfold zs. induction l as [|x l IH]; intros [|y l'] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma ha_zs_zb : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. inversion H; subst.
  unfold zs, zb in *. cbn [map]. rewrite ha_u8 by assumption. f_equal. apply IH. assumption.
Qed.

Lemma ha_find_byte_zb : forall c l, Forall (fun x => 0 <= x < 256) l -> find_byte c (zb l) = memchr l c.
Proof.
  intros c. induction l as [|x l IH]; intros H; [reflexivity|]. inversion H; subst.
  unfold zb. cbn [map find_byte memchr]. rewrite ha_u8 by assumption.
  destruct (x =? c); [reflexivity|]. fold (zb l). rewrite IH by assumption.
  destruct (memchr l c); reflexivity.
Qed.

Lemma ha_memchr_res : forall A c n l, Forall (fun x => 0 <= x < 256) l -> n = Z.of_nat (length l) ->
  memchr_res A c n (zb l) = match memchr l c with Some k => A + Z.of_nat k | None => 0 end.
Proof.
  intros A c n l H ->. unfold memchr_res. rewrite Nat2Z.id.
  rewrite firstn_all2 by (unfold zb; rewrite length_map; lia).
  rewrite ha_find_byte_zb by exact H. reflexivity.
Qed.

Lemma ha_memchr_ok : forall A c n buf, n <= Z.of_nat (length buf) -> memchr_ok A c n buf.
Proof. intros A c n buf H. unfold memchr_ok. destruct (find_byte _ _); [left|]; lia. Qed.

Lemma ha_munch_nil : forall (m m' : word -> option byte), munch [] m m' -> m' = m.
Proof. intros m m' H. apply functional_extensionality. intros x. apply H. exact I. Qed.

Lemma ha_blank_le32 : forall c, blank c = true -> c <= 32.
Proof.
  intros c H. unfold blank in H.
  destruct (c =? 32) eqn:E1; [apply Z.eqb_eq in E1; lia|].
  destruct (c =? 9) eqn:E2; [apply Z.eqb_eq in E2; lia|].
  destruct (c =? 13) eqn:E3; [apply Z.eqb_eq in E3; lia|]. discriminate.
Qed.

(** The loops' blank test: `bltu s11 (32), c` (out when c > 32), then bit c of s9 = 0x100002200 (`srl`, `andi 1`). *)
Lemma ha_mask_b : forall c, 0 <= c <= 32 ->
  (Z.land (Z.shiftr 4294976000 (c mod 64)) 1 =? 0) = negb (blank c).
Proof.
  intros c Hc. destruct (Z_of_nat_complete c ltac:(lia)) as [n ->].
  assert (Hn : (n <= 32)%nat) by lia. clear Hc.
  do 33 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma ha_mask0 : forall c, 0 <= c <= 32 -> Z.land (Z.shiftr 4294976000 (c mod 64)) 1 = 0 -> blank c = false.
Proof.
  intros c Hc H. pose proof (ha_mask_b c Hc) as E. apply Z.eqb_eq in H. rewrite H in E.
  destruct (blank c); [discriminate | reflexivity].
Qed.

Lemma ha_mask1 : forall c, 0 <= c <= 32 -> Z.land (Z.shiftr 4294976000 (c mod 64)) 1 <> 0 -> blank c = true.
Proof.
  intros c Hc H. pose proof (ha_mask_b c Hc) as E. apply Z.eqb_neq in H. rewrite H in E.
  destruct (blank c); [reflexivity | discriminate].
Qed.

Lemma ha_not_blank_gt : forall c, 32 < c -> blank c = false.
Proof.
  intros c H. destruct (blank c) eqn:B; [apply ha_blank_le32 in B; lia | reflexivity].
Qed.

Lemma ha_signed_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit by lia.
  destruct (Z.ltb_spec0 z (2 ^ 63)); lia.
Qed.

Lemma ha_forall_skipn : forall (P : Z -> Prop) (l : list Z) k, Forall P l -> Forall P (skipn k l).
Proof.
  intros P. induction l as [|x l IH]; intros [|k] H; cbn [skipn]; auto. inversion H; subst. apply IH. assumption.
Qed.

Lemma ha_forall_firstn : forall (P : Z -> Prop) (l : list Z) k, Forall P l -> Forall P (firstn k l).
Proof.
  intros P. induction l as [|x l IH]; intros [|k] H; cbn [firstn]; auto. inversion H; subst.
  constructor; [assumption | apply IH; assumption].
Qed.

Lemma ha_forall_slice : forall (P : Z -> Prop) (l : list Z) a b, Forall P l -> Forall P (slice a b l).
Proof. intros P l a b H. unfold slice. apply ha_forall_firstn, ha_forall_skipn, H. Qed.

Lemma ha_nth_range : forall l, Forall (fun x => 0 <= x < 256) l -> forall q, 0 <= nth q l 0 < 256.
Proof.
  intros l H q. destruct (Nat.lt_ge_cases q (length l)) as [Hq|Hq].
  - rewrite Forall_forall in H. apply H. apply nth_In. exact Hq.
  - rewrite nth_overflow by exact Hq. lia.
Qed.

Lemma ha_firstn_slice : forall (l : list Z) x y k, (k <= y - x)%nat -> firstn k (slice x y l) = slice x (x + k) l.
Proof.
  intros l x y k H. unfold slice. rewrite firstn_firstn.
  replace (Nat.min k (y - x)) with k by lia. replace (x + k - x)%nat with k by lia. reflexivity.
Qed.

Lemma ha_skipn_slice : forall (l : list Z) x y k, (k <= y - x)%nat -> skipn k (slice x y l) = slice (x + k) y l.
Proof.
  intros l x y k H. unfold slice. rewrite skipn_firstn_comm, skipn_skipn.
  replace (y - (x + k))%nat with (y - x - k)%nat by lia. rewrite (Nat.add_comm k x). reflexivity.
Qed.

(** The line inside the text left. *)
Lemma ha_line_props : forall rest, Forall (fun x => 0 <= x < 256) rest ->
  (length (mf_line rest) <= length rest)%nat /\ Forall (fun x => 0 <= x < 256) (mf_line rest).
Proof.
  intros rest H. destruct (mf_line_rest rest) as [[E _]|[E _]].
  - rewrite E in H. apply Forall_app in H as [H _]. split; [|exact H].
    rewrite E at 2. rewrite length_app. cbn [length]. lia.
  - rewrite E in H. split; [rewrite E at 2; lia | exact H].
Qed.

(** ** The text's bytes and placement *)
Lemma ha_rd_slice : forall m sp0 lo c p rest x y, mf_text m sp0 lo c p rest -> (x <= y <= length (mf_line rest))%nat ->
  forall q, (q < y - x)%nat ->
  ov_read_bytes rsegs m (wa (p + Z.of_nat x + Z.of_nat q)) 1 = Some [Z_to_bv 8 (nth q (slice x y (mf_line rest)) 0)].
Proof.
  intros m sp0 lo c p rest x y TXT Hxy q Hq.
  pose proof TXT as T. apply mf_text_props in T. destruct T as (_ & RNG & _).
  destruct (ha_line_props rest RNG) as [LL _].
  rewrite slice_nth by lia. rewrite <- mf_line_nth by lia.
  replace (p + Z.of_nat x + Z.of_nat q) with (p + Z.of_nat (x + q)) by lia.
  apply (mf_text_byte m sp0 lo c p rest (x + q) TXT). lia.
Qed.

Lemma ha_bytes_slice : forall m sp0 lo c p rest x y, mf_text m sp0 lo c p rest -> (x <= y <= length (mf_line rest))%nat ->
  bytes_at rsegs m (p + Z.of_nat x) (zb (slice x y (mf_line rest))).
Proof.
  intros m sp0 lo c p rest x y TXT Hxy.
  pose proof TXT as T. apply mf_text_props in T. destruct T as (_ & RNG & _).
  destruct (ha_line_props rest RNG) as [LL _].
  pose proof (mf_text_bytes m sp0 lo c p rest x (y - x) TXT ltac:(lia)) as B.
  rewrite (mf_line_firstn rest x (y - x)) in B by lia. replace (x + (y - x))%nat with y in B by lia. exact B.
Qed.

Lemma ha_text_apart : forall m sp0 lo c p rest o k sp, mf_text m sp0 lo c p rest -> (o + k <= length rest)%nat ->
  sp <= sp0 -> apart (p + Z.of_nat o) (Z.of_nat k) lo sp.
Proof. intros m sp0 lo c p rest o k sp (P0 & BN & CS & AP & AC) Hk Hsp. unfold apart in *. lia. Qed.

(** The string "segment" at 0x10313 in .rodata (ieq's third argument at 0x14400), with its slack. *)
Lemma ha_seg_lit : forall m, mem_inv rsegs m -> cstr_at rsegs m 0x10313 S_segment.
Proof.
  intros m HI.
  lazymatch eval vm_compute in (image_bytes rsegs 0x10313 13) with
  | Some ?bs =>
      pose proof (ro_cells_image rsegs m 0x10313 bs HI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO;
      exists (firstn 7 bs), (skipn 8 bs);
      assert (E : bs = firstn 7 bs ++ ZERO :: skipn 8 bs) by (apply ha_zs_inj; vm_compute; reflexivity)
  end.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO.
  assert (ES : S_segment = [115; 101; 103; 109; 101; 110; 116]) by (vm_compute; reflexivity).
  split; [eapply bytes_at_ext; [exact RO | exact E]|].
  split; [rewrite ES; vm_compute; reflexivity|].
  split; [rewrite ES; cbn [In]; lia|].
  rewrite ES. vm_compute. congruence.
Qed.

(** ** The loop facts across a callee or a store *)
Lemma ha_ctx_stack : forall m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 k,
  mf_ctx m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 -> k <= M_FILE_STACK - M_FILE_FRAME ->
  stack_ok rsegs m lo sp k.
Proof.
  intros m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 k CTX Hk.
  pose proof CTX as B. apply mf_ctx_bounds in B. destruct B as (IMG & LOS & SP63 & SP016 & SP16 & _ & C0 & CE).
  destruct CTX as (E0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SOK & _).
  destruct SOK as (STK & _ & _ & RO).
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *.
  split; [apply (stk_split rsegs m lo sp sp0 STK); lia|].
  split; [lia|]. split; [exact SP16|]. intros a Ha. apply RO. lia.
Qed.

Lemma ha_stk_store_ok : forall m lo hi a (j : nat), stk rsegs m lo hi -> lo <= a -> a + Z.of_nat j <= hi ->
  store_ok rsegs m (wa a) j = true.
Proof.
  intros m lo hi a j (H0 & H1 & H) Ha Hj.
  assert (W : wr_at rsegs m a (Z.of_nat j)).
  { split; [lia|]. split; [lia|]. intros i Hi. destruct (H (a + i) ltac:(lia)) as [Hw _]. exact Hw. }
  pose proof (wr_at_store_ok rsegs m a (Z.of_nat j) 0 j W ltac:(lia) ltac:(lia)) as R.
  rewrite Z.add_0_r in R. exact R.
Qed.

(** ieq writes only its frame [sp - 32, sp): the loop facts hold on its memory. *)
Lemma ha_loop_ieq : forall m m' fc sp0 sp lo c p mc cur line k0 rest
    ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  m_file_loop m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  munch [(sp - IEQ_STACK, sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo sp ->
  m_file_loop m' fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros m m' fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 HL MU WM MI STK.
  apply mf_loop_iff in HL. destruct HL as (CTX & TXT & ST). apply mf_loop_iff.
  pose proof CTX as B. apply mf_ctx_bounds in B. destruct B as (IMG & LOS & SP63 & SP016 & SP16 & CAP & C0 & CE).
  pose proof CTX as (E0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PE & _ & _ & SOK & _).
  destruct SOK as (STK0 & _ & _ & _). destruct PE as (FRM & _).
  destruct ST as (MC & CUR & CUROK & K0 & L0 & LB & RF & OV).
  unfold IEQ_STACK, M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *.
  assert (SUB : sub_fp [(sp - 32, sp)] [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)]).
  { intros x Hx. cbn [outside] in *. destruct Hx as (H1 & _). split; [lia | exact I]. }
  assert (TM : MemNorm.task_mem rsegs m') by (eapply mf_task_mem with (pend := false); [exact CTX | exact MC | exact MU | exact SUB]).
  assert (STK' : stk rsegs m' lo sp0).
  { eapply mf_stk_after; [exact STK0 | exact MU | exact WM | exact STK | lia |]. cbn [disjoint_from]. split; [lia | exact I]. }
  split; [eapply mf_ctx_transport; eassumption|].
  split; [eapply mf_text_transport; [exact TXT | exact MU |]; intros x Hx; cbn [outside] in *;
          destruct Hx as (H1 & _); split; [lia | exact I]|].
  split; [eapply mconf_atp_transport with (pend := false); [exact MC | exact MU |]; cbn [disjoint_from];
          split; [lia | exact I]|].
  split; [eapply cell8_transport; [exact CUR | exact MU |]; cbn [disjoint_from]; split; [lia | exact I]|].
  exact (conj CUROK (conj K0 (conj L0 (conj LB (conj RF OV))))).
Qed.

(** `sd zero, 0x20(sp)` (cur = NULL, 0x14648 / 0x144cc): the store is allowed, and the loop facts hold after it. *)
Lemma ha_null_facts : forall m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 p rest mc pend,
  mf_ctx m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 -> mf_text m sp0 lo c p rest ->
  mconf_atp rsegs pend m c mc ->
  store_ok rsegs m (wa (sp + 32)) 8 = true /\
  (forall m'', m'' = write_to_mem m (wa (sp + 32)) (le8 (Z_to_bv 64 0)) ->
   mf_ctx m'' fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 /\ mf_text m'' sp0 lo c p rest /\
   mconf_atp rsegs pend m'' c mc /\ cell8 m'' (sp + 0x20) 0 /\
   munch [(sp + 0x20, sp + 0x28)] m m'' /\ wmono rsegs m m'').
Proof.
  intros m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 p rest mc pend CTX TXT MC.
  pose proof CTX as B. apply mf_ctx_bounds in B. destruct B as (IMG & LOS & SP63 & SP016 & SP16 & CAP & C0 & CE).
  pose proof CTX as (E0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PE & _ & _ & SOK & MI).
  destruct SOK as (STK & _ & _ & _). destruct PE as (FRM & _).
  pose proof STK as (LO0 & _ & _).
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *.
  assert (SO : store_ok rsegs m (wa (sp + 32)) 8 = true) by (apply (ha_stk_store_ok m lo sp0); [exact STK | lia | lia]).
  split; [exact SO|]. intros m'' ->.
  assert (L8 : length (le8 (Z_to_bv 64 0)) = 8%nat) by reflexivity.
  assert (MU : munch [(sp + 0x20, sp + 0x28)] m (write_to_mem m (wa (sp + 32)) (le8 (Z_to_bv 64 0)))).
  { apply munch_write; [apply munch_refl | lia | rewrite L8; lia | cbn [inside]; rewrite L8; left; lia]. }
  assert (WM : wmono rsegs m (write_to_mem m (wa (sp + 32)) (le8 (Z_to_bv 64 0)))) by (apply wmono_write, wmono_refl).
  assert (MI' : mem_inv rsegs (write_to_mem m (wa (sp + 32)) (le8 (Z_to_bv 64 0)))).
  { apply mem_inv_store; [exact MI | rewrite L8; exact SO]. }
  assert (SUB : sub_fp [(sp + 0x20, sp + 0x28)] [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)]).
  { intros x Hx. cbn [outside] in *. destruct Hx as (_ & H2 & _). split; [lia | exact I]. }
  assert (TM : MemNorm.task_mem rsegs (write_to_mem m (wa (sp + 32)) (le8 (Z_to_bv 64 0)))).
  { eapply mf_task_mem; [exact CTX | exact MC | exact MU | exact SUB]. }
  assert (STK' : stk rsegs (write_to_mem m (wa (sp + 32)) (le8 (Z_to_bv 64 0))) lo sp0).
  { apply stk_write; [exact STK | lia | rewrite L8; lia]. }
  split; [eapply mf_ctx_transport; eassumption|].
  split; [eapply mf_text_transport; [exact TXT | exact MU |]; intros x Hx; cbn [outside] in *;
          destruct Hx as (H1 & _); split; [lia | exact I]|].
  split; [eapply mconf_atp_transport; [exact MC | exact MU |]; cbn [disjoint_from]; split; [lia | exact I]|].
  split; [unfold cell8; apply bytes_at_write_same; [lia | rewrite L8; lia]|].
  split; [exact MU | exact WM].
Qed.

(** ** The tail 0x143d4 with the line's state: the premise H_MF_TAIL for the next line. *)
Lemma ha_at_tail : forall n, H_MF_TAIL n ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc' : mconf) (cur' : option nat) (k0 : nat) (rest : list Z),
    (length rest <= n)%nat -> rest <> [] ->
    mf_ctx m fc (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    mf_text m (bv_unsigned sp0) lo c p rest ->
    mconf_at rsegs m c mc' -> cell8 m (bv_unsigned sp + 0x20) (cur_ptr c cur') -> cur_ok mc' cur' ->
    (k0 <= length (mc_kept mc'))%nat -> 0 <= line -> line + Z.of_nat (length rest) <= 65535 ->
    mc_refused mc' + Z.of_nat (length (mf_rest rest)) < 2 ^ 32 ->
    mc_overflow mc' + Z.of_nat (length (mf_rest rest)) < 2 ^ 32 ->
    m_file_regs c (mf_next p rest) (line + 1) s0 s1 s2 s3 s7 s8 s9 s10 s11 ->
    evt rsegs
      (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0 (mf_fin (mc', cur') line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x143d4) fc None m (seg_rom rsegs)).
Proof.
  intros n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc' cur' k0 rest
    HL HNE CTX TXT MC CUR CUROK K0 L0 LB RF OV REGS.
  unfold mf_post, mf_fin. unfold H_MF_TAIL in HT.
  eapply HT; [ | eapply mf_tail_loop; eassumption | exact REGS ].
  pose proof (mf_rest_lt rest HNE). lia.
Qed.

Lemma ha_refuse_cnt : forall c l k,
  mc_refused (m_refuse c l k) = mc_refused c + 1 /\ mc_overflow (m_refuse c l k) = mc_overflow c.
Proof. intros c l k. split; reflexivity. Qed.

(** ** The strip loops *)
Section Loops.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s10 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (u : list Z) (A : Z).
Hypothesis RG : forall q, 0 <= nth q u 0 < 256.
Hypothesis RD : forall q, (q < length u)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat q)) 1 = Some [Z_to_bv 8 (nth q u 0)].
Hypothesis HA : 0 < A.
Hypothesis HAL : A + Z.of_nat (length u) < 2 ^ 64.

(** Forward loop of the first strip, 0x141b4: s6 = A + k, the bytes before k blank; s4 = s5 = A + |u|. *)
Lemma ha_f1 : forall (d k : nat) (a0 a1 s4 s5 s6 s7 : word),
  (length u - k = d)%nat -> (k < length u)%nat -> all_blank u 0 k ->
  s4 = Z_to_bv 64 (A + Z.of_nat (length u)) -> s5 = s4 -> s6 = Z_to_bv 64 (A + Z.of_nat k) ->
  (forall (fb : nat) (a0' w6 : word), (fb <= length u)%nat -> all_blank u 0 fb ->
     (fb = length u \/ blank (nth fb u 0) = false) -> w6 = Z_to_bv 64 (A + Z.of_nat fb) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 w6 s7 s8
                         (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x141d4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                      (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x141b4) fc None m (seg_rom rsegs)).
Proof using RG RD HA HAL.
  induction d as [|d IH]; intros k a0 a1 s4 s5 s6 s7 Hd Hk HB E4 E5 E6 K; [lia|]. subst s4 s5 s6.
  pose proof (RG k) as Rc. pose proof (RD k Hk) as RDk.
  zstep. zstep. if_cases Hc1; zify_cond Hc1; rewrite ?ha_u8 in Hc1 by exact Rc.
  - apply (K k); [lia | exact HB | right; apply ha_not_blank_gt; lia | reflexivity].
  - zstep. zstep. zstep. if_cases Hc2; zify_cond Hc2; rewrite ?ha_u8 in Hc2 by exact Rc.
    + apply (K k); [lia | exact HB | right; apply ha_mask0; [lia | exact Hc2] | reflexivity].
    + apply ha_mask1 in Hc2; [|lia].
      assert (HB' : all_blank u 0 (S k)).
      { intros q Hq. destruct (Nat.eq_dec q k) as [->|]; [exact Hc2 | apply HB; lia]. }
      zstep. zstep. if_cases Hc3; zify_cond Hc3; rewrite ?unsigned_lit in Hc3 by lia.
      * eapply (IH (S k)); [lia | lia | exact HB' | reflexivity | reflexivity | word_eq_tac | exact K].
      * zstep. apply (K (length u)); [lia | | left; reflexivity | word_eq_tac].
        replace (length u) with (S k) by lia. exact HB'.
Qed.

(** Backward loop of the first strip, 0x141d8: s4 = A + e, the bytes from e blank, fb < e. Out at 0x143e4 with
    s5 = 9 (0x143e0, or 0x141f4 when it reaches fb). *)
Lemma ha_b1 : forall (d e fb : nat) (a0 a1 s4 s5 s6 s7 : word),
  (e - fb = d)%nat -> (fb < e)%nat -> (e <= length u)%nat ->
  all_blank u 0 fb -> (fb = length u \/ blank (nth fb u 0) = false) -> all_blank u e (length u) ->
  s4 = Z_to_bv 64 (A + Z.of_nat e) -> s6 = Z_to_bv 64 (A + Z.of_nat fb) ->
  (forall (be : nat) (a0' w4 : word), (fb <= be <= length u)%nat -> h_strip u = slice fb be u ->
     w4 = Z_to_bv 64 (A + Z.of_nat be) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 w4 (Z_to_bv 64 9) s6 s7 s8
                         (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x143e4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                      (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x141d8) fc None m (seg_rom rsegs)).
Proof using RG RD HA HAL.
  induction d as [|d IH]; intros e fb a0 a1 s4 s5 s6 s7 Hd Hfe HeL HB0 HBf HBe E4 E6 K; [lia|]. subst s4 s6.
  pose proof (RG (e - 1)) as Rc.
  pose proof (RD (e - 1) ltac:(lia)) as RDk.
  replace (A + Z.of_nat (e - 1)) with (A + Z.of_nat e + -1) in RDk by lia.
  zstep. zstep. if_cases Hc1; zify_cond Hc1; rewrite ?ha_u8 in Hc1 by exact Rc.
  - zstep. apply (K e); [lia | | reflexivity].
    apply h_strip_idx; [lia | exact HB0 | exact HBf | exact HBe | right; apply ha_not_blank_gt; lia].
  - zstep. zstep. zstep. if_cases Hc2; zify_cond Hc2; rewrite ?ha_u8 in Hc2 by exact Rc.
    + zstep. apply (K e); [lia | | reflexivity].
      apply h_strip_idx; [lia | exact HB0 | exact HBf | exact HBe | right; apply ha_mask0; [lia | exact Hc2]].
    + apply ha_mask1 in Hc2; [|lia].
      assert (HBe' : all_blank u (e - 1) (length u)).
      { intros q Hq'. destruct (Nat.eq_dec q (e - 1)) as [->|]; [exact Hc2 | apply HBe; lia]. }
      zstep. zstep. if_cases Hc3; zify_cond Hc3; rewrite ?unsigned_lit in Hc3 by lia.
      * eapply (IH (e - 1)%nat fb); [lia | lia | lia | exact HB0 | exact HBf | exact HBe' | word_eq_tac
                                   | reflexivity | exact K].
      * zstep. zstep. zstep. apply (K fb); [lia | | reflexivity].
        replace (e - 1)%nat with fb in HBe' by lia.
        apply h_strip_idx; [lia | exact HB0 | exact HBf | exact HBe' | left; reflexivity].
Qed.

(** 0x141d4: the backward loop's test (fb = |u|: nothing left, to 0x143e0). *)
Lemma ha_b1e : forall (fb : nat) (a0 a1 s4 s5 s6 s7 : word),
  (fb <= length u)%nat -> all_blank u 0 fb -> (fb = length u \/ blank (nth fb u 0) = false) ->
  s4 = Z_to_bv 64 (A + Z.of_nat (length u)) -> s6 = Z_to_bv 64 (A + Z.of_nat fb) ->
  (forall (be : nat) (a0' w4 : word), (fb <= be <= length u)%nat -> h_strip u = slice fb be u ->
     w4 = Z_to_bv 64 (A + Z.of_nat be) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 w4 (Z_to_bv 64 9) s6 s7 s8
                         (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x143e4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                      (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x141d4) fc None m (seg_rom rsegs)).
Proof using RG RD HA HAL.
  intros fb a0 a1 s4 s5 s6 s7 Hfb HB0 HBf E4 E6 K. subst s4.
  pose proof E6 as E6'. subst s6.
  zstep. if_cases Hc; zify_cond Hc; rewrite ?unsigned_lit in Hc by lia.
  - assert (Efb : fb = length u) by lia. subst fb.
    zstep. apply (K (length u)); [lia | | reflexivity].
    apply h_strip_idx; [lia | exact HB0 | left; reflexivity | intros q Hq; lia | left; reflexivity].
  - eapply (ha_b1 (length u - fb) (length u) fb); [lia | lia | lia | exact HB0 | exact HBf | intros q Hq; lia
                                                   | reflexivity | reflexivity | exact K].
Qed.

(** The first strip from 0x141a4: s5 = the '[' at A - 1, s4 = the ']' at A + |u|. Out at 0x143e4 with s6 = b,
    s4 = be, s5 = 9: h_strip u = the bytes [fb, be) of u. *)
Lemma ha_strip1 : forall (a0 a1 s4 s5 s6 s7 : word),
  s5 = Z_to_bv 64 (A - 1) -> s4 = Z_to_bv 64 (A + Z.of_nat (length u)) ->
  (forall (fb be : nat) (a0' w4 w6 : word), (fb <= be <= length u)%nat -> h_strip u = slice fb be u ->
     w4 = Z_to_bv 64 (A + Z.of_nat be) -> w6 = Z_to_bv 64 (A + Z.of_nat fb) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 w4 (Z_to_bv 64 9) w6 s7 s8
                         (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x143e4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                      (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x141a4) fc None m (seg_rom rsegs)).
Proof using RG RD HA HAL.
  intros a0 a1 s4 s5 s6 s7 E5 E4 K. subst s4 s5.
  zstep. zstep. if_cases Hc; zify_cond Hc; rewrite ?unsigned_lit in Hc by lia.
  - eapply (ha_b1e 0); [lia | intros q Hq; lia | left; lia | reflexivity | word_eq_tac |].
    intros be a0' w4 Hbe HS E4. apply (K 0%nat be a0' w4); [lia | exact HS | exact E4 | word_eq_tac].
  - zstep. zstep.
    eapply (ha_f1 (length u - 0) 0); [lia | lia | intros q Hq; lia | reflexivity | word_eq_tac | word_eq_tac |].
    intros fb a0' w6 Hfb HB0 HBf E6.
    eapply (ha_b1e fb); [exact Hfb | exact HB0 | exact HBf | reflexivity | exact E6 |].
    intros be a0'' w4 Hbe HS E4. apply (K fb be a0'' w4 w6); [lia | exact HS | exact E4 | exact E6].
Qed.

(** Forward loop of the second strip, 0x14424: s5 = A + k, the count s7 = |u| - k; s4 = s6 = A + |u|. *)
Lemma ha_f2 : forall (d k : nat) (a0 a1 s4 s5 s6 s7 : word),
  (length u - k = d)%nat -> (k < length u)%nat -> all_blank u 0 k ->
  s4 = Z_to_bv 64 (A + Z.of_nat (length u)) -> s6 = s4 -> s5 = Z_to_bv 64 (A + Z.of_nat k) ->
  s7 = Z_to_bv 64 (Z.of_nat (length u - k)) ->
  (forall (fb : nat) (a0' w5 w7 : word), (fb <= length u)%nat -> all_blank u 0 fb ->
     (fb = length u \/ blank (nth fb u 0) = false) -> w5 = Z_to_bv 64 (A + Z.of_nat fb) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 w5 s6 w7 s8
                         (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14448) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                      (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x14424) fc None m (seg_rom rsegs)).
Proof using RG RD HA HAL.
  induction d as [|d IH]; intros k a0 a1 s4 s5 s6 s7 Hd Hk HB E4 E6 E5 E7 K; [lia|]. subst s4 s5 s6 s7.
  pose proof (RG k) as Rc. pose proof (RD k Hk) as RDk.
  zstep. zstep. if_cases Hc1; zify_cond Hc1; rewrite ?ha_u8 in Hc1 by exact Rc.
  - apply (K k); [lia | exact HB | right; apply ha_not_blank_gt; lia | reflexivity].
  - zstep. zstep. zstep. if_cases Hc2; zify_cond Hc2; rewrite ?ha_u8 in Hc2 by exact Rc.
    + apply (K k); [lia | exact HB | right; apply ha_mask0; [lia | exact Hc2] | reflexivity].
    + apply ha_mask1 in Hc2; [|lia].
      assert (HB' : all_blank u 0 (S k)).
      { intros q Hq. destruct (Nat.eq_dec q k) as [->|]; [exact Hc2 | apply HB; lia]. }
      zstep. zstep. zstep. if_cases Hc3; zify_cond Hc3; rewrite ?unsigned_lit in Hc3 by lia.
      * eapply (IH (S k)); [lia | lia | exact HB' | reflexivity | reflexivity | word_eq_tac | word_eq_tac
                           | exact K].
      * zstep. apply (K (length u)); [lia | | left; reflexivity | word_eq_tac].
        replace (length u) with (S k) by lia. exact HB'.
Qed.

(** Backward loop of the second strip, 0x14458: s4 = A + e, a0 = s5 = A + fb, fb < e, the bytes from e blank. *)
Lemma ha_b2 : forall (d e fb : nat) (a0 a1 s4 s5 s6 : word),
  (e - fb = d)%nat -> (fb < e)%nat -> (e <= length u)%nat ->
  all_blank u 0 fb -> (fb = length u \/ blank (nth fb u 0) = false) -> all_blank u e (length u) ->
  s4 = Z_to_bv 64 (A + Z.of_nat e) -> s5 = Z_to_bv 64 (A + Z.of_nat fb) -> a0 = s5 ->
  (forall (be : nat) (a0' a1' w4 : word), (fb <= be <= length u)%nat -> h_strip u = slice fb be u ->
     w4 = Z_to_bv 64 (A + Z.of_nat be) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 w4 s5 s6 (Z_to_bv 64 9) s8
                         (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14478) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 9) s8
                      (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x14458) fc None m (seg_rom rsegs)).
Proof using RG RD HA HAL.
  induction d as [|d IH]; intros e fb a0 a1 s4 s5 s6 Hd Hfe HeL HB0 HBf HBe E4 E5 E0 K; [lia|].
  subst s4 a0. pose proof E5 as E5'. subst s5.
  pose proof (RG (e - 1)) as Rc.
  pose proof (RD (e - 1) ltac:(lia)) as RDk.
  replace (A + Z.of_nat (e - 1)) with (A + Z.of_nat e + -1) in RDk by lia.
  zstep. zstep. if_cases Hc1; zify_cond Hc1; rewrite ?ha_u8 in Hc1 by exact Rc.
  - apply (K e); [lia | | reflexivity].
    apply h_strip_idx; [lia | exact HB0 | exact HBf | exact HBe | right; apply ha_not_blank_gt; lia].
  - zstep. zstep. zstep. if_cases Hc2; zify_cond Hc2; rewrite ?ha_u8 in Hc2 by exact Rc.
    + apply (K e); [lia | | reflexivity].
      apply h_strip_idx; [lia | exact HB0 | exact HBf | exact HBe | right; apply ha_mask0; [lia | exact Hc2]].
    + apply ha_mask1 in Hc2; [|lia].
      assert (HBe' : all_blank u (e - 1) (length u)).
      { intros q Hq'. destruct (Nat.eq_dec q (e - 1)) as [->|]; [exact Hc2 | apply HBe; lia]. }
      zstep. zstep. if_cases Hc3; zify_cond Hc3; rewrite ?unsigned_lit in Hc3 by lia.
      * eapply (IH (e - 1)%nat fb); [lia | lia | lia | exact HB0 | exact HBf | exact HBe' | word_eq_tac
                                   | reflexivity | reflexivity | exact K].
      * zstep. apply (K fb); [lia | | reflexivity].
        replace (e - 1)%nat with fb in HBe' by lia.
        apply h_strip_idx; [lia | exact HB0 | exact HBf | exact HBe' | left; reflexivity].
Qed.

(** 0x14448: s7 = 9, the backward loop's test, a0 = s5. *)
Lemma ha_b2e : forall (fb : nat) (a0 a1 s4 s5 s6 s7 : word),
  (fb <= length u)%nat -> all_blank u 0 fb -> (fb = length u \/ blank (nth fb u 0) = false) ->
  s4 = Z_to_bv 64 (A + Z.of_nat (length u)) -> s5 = Z_to_bv 64 (A + Z.of_nat fb) ->
  (forall (be : nat) (a0' a1' w4 : word), (fb <= be <= length u)%nat -> h_strip u = slice fb be u ->
     w4 = Z_to_bv 64 (A + Z.of_nat be) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 w4 s5 s6 (Z_to_bv 64 9) s8
                         (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14478) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                      (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x14448) fc None m (seg_rom rsegs)).
Proof using RG RD HA HAL.
  intros fb a0 a1 s4 s5 s6 s7 Hfb HB0 HBf E4 E5 K. subst s4.
  pose proof E5 as E5'. subst s5.
  zstep. zstep. if_cases Hc; zify_cond Hc; rewrite ?unsigned_lit in Hc by lia.
  - assert (Efb : fb = length u) by lia. subst fb.
    apply (K (length u)); [lia | | reflexivity].
    apply h_strip_idx; [lia | exact HB0 | left; reflexivity | intros q Hq; lia | left; reflexivity].
  - zstep. zstep.
    eapply (ha_b2 (length u - fb) (length u) fb); [lia | lia | lia | exact HB0 | exact HBf | intros q Hq; lia
                                                   | reflexivity | reflexivity | word_eq_tac | exact K].
Qed.

(** The second strip from 0x14414: s6 = b = A - 7, s4 = be = A + |u|, s7 = be - b; |u| >= 1 (be - b >= 8). Out at
    0x14478 with s5 = the name's start, s4 = its end, s7 = 9. *)
Lemma ha_strip2 : forall (a0 a1 s4 s5 s6 s7 : word),
  7 <= A -> (1 <= length u)%nat ->
  s6 = Z_to_bv 64 (A - 7) -> s4 = Z_to_bv 64 (A + Z.of_nat (length u)) ->
  s7 = Z_to_bv 64 (Z.of_nat (length u) + 7) ->
  (forall (fb be : nat) (a0' a1' w4 w5 w6 : word), (fb <= be <= length u)%nat -> h_strip u = slice fb be u ->
     w4 = Z_to_bv 64 (A + Z.of_nat be) -> w5 = Z_to_bv 64 (A + Z.of_nat fb) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 w4 w5 w6 (Z_to_bv 64 9) s8
                         (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14478) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                      (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x14414) fc None m (seg_rom rsegs)).
Proof using RG RD HA HAL.
  intros a0 a1 s4 s5 s6 s7 H7 Hu E6 E4 E7 K. subst s4 s6 s7.
  zstep. zstep. if_cases Hc; zify_cond Hc; rewrite ?unsigned_lit in Hc by lia; [exfalso; lia|].
  zstep. zstep.
  eapply (ha_f2 (length u - 0) 0); [lia | lia | intros q Hq; lia | reflexivity | word_eq_tac | word_eq_tac
                                    | word_eq_tac |].
  intros fb a0' w5 w7 Hfb HB0 HBf E5.
  eapply (ha_b2e fb); [exact Hfb | exact HB0 | exact HBf | reflexivity | exact E5 |].
  intros be a0'' a1' w4 Hbe HS E4. eapply (K fb be a0'' a1' w4 w5); [lia | exact HS | exact E4 | exact E5].
Qed.

End Loops.

(** ** The two refusals: m_refuse(c, line + 1), cur = NULL, then the tail with (m_refuse mc (line + 1) false,
    None). The facts are the cut's (the memory before the call: the cut's, or ieq's after it). *)
Lemma ha_ref_1463c : m_refuse_contract -> forall n, H_MF_TAIL n ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    m_file_regs c (mf_next p rest) (line + 1) s0 s1 s2 s3 s7 s8 s9 s10 s11 ->
    evt rsegs
      (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (m_refuse mc (line + 1) false, None) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1463c) fc None m (seg_rom rsegs)).
Proof.
  intros HMR n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest HL HNE HLOOP HREGS.
  apply mf_loop_iff in HLOOP. destruct HLOOP as (CTX & TXT & ST).
  destruct ST as (MC & CUR & CUROK & K0 & L0 & LB & RF & OV).
  assert (LR : (1 <= length rest)%nat) by (destruct rest; [congruence | cbn [length]; lia]).
  pose proof CTX as B. apply mf_ctx_bounds in B. destruct B as (IMG & LOS & SP63 & SP016 & SP16 & _ & C0 & CE).
  pose proof CTX as (ESP & _).
  pose proof HREGS as (Er0 & Er1 & Er2 & Er3 & _). subst s0 s3.
  (* 0x1463c a0 = c; 0x14640 a1 = line + 1; 0x14644 jal m_refuse *)
  step. step. step.
  eapply (mf_refuse_call HMR 0x14644) with (knock := false) (mc := mc);
    [lia | lia | reflexivity | exact CTX | exact TXT | exact CUR | exact MC | lia | lia | ].
  intros m1 F1 fc1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 CTX1 TXT1 CUR1 MC1 MU1 WM1 HF1.
  eapply mf_post_back; [exact HF1 | exact MU1 | exact WM1 | |].
  { apply (sub_fp_trans _ (M_FILE_W (bv_unsigned sp0) c k0 (m_refuse mc (line + 1) false))).
    - apply mf_W_refuse; unfold M_FILE_STACK, M_REFUSE_STACK, M_FILE_FRAME in *; [lia | lia | exact K0].
    - apply (mf_W_fin _ _ _ (m_refuse mc (line + 1) false, None)). exact I. }
  replace (0x14644 + 4) with 0x14648 by reflexivity.
  destruct (ha_null_facts m1 fc1 (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
              p rest (m_refuse mc (line + 1) false) false CTX1 TXT1 MC1) as (SO & NF).
  (* 0x14648 sd zero, 0x20(sp) *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bb) _) =>
    replace (write_to_mem mm aa bb) with (write_to_mem m1 (wa (bv_unsigned sp + 32)) (le8 (Z_to_bv 64 0)))
      by (f_equal; first [reflexivity | unfold wa; word_eq_tac])
  end.
  remember (write_to_mem m1 (wa (bv_unsigned sp + 32)) (le8 (Z_to_bv 64 0))) as m2 eqn:Em2.
  destruct (NF m2 eq_refl) as (CTX2 & TXT2 & MC2 & CUR2 & MU2 & WM2). clear Em2 NF.
  eapply mf_post_back; [intros k Hk; reflexivity | exact MU2 | exact WM2
                       | apply mf_W_frame; unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *; lia | ].
  (* 0x1464c j 0x143d4 *)
  step.
  pose proof (m_refuse_sizes mc (line + 1) false) as (_ & SZ).
  pose proof (ha_refuse_cnt mc (line + 1) false) as (RC1 & RC2).
  pose proof (mf_rest_lt rest HNE) as RLT.
  eapply (ha_at_tail n HT); [exact HL | exact HNE | exact CTX2 | exact TXT2 | exact MC2 | exact CUR2 | exact I
                            | lia | lia | lia | | | exact HREGS].
  - eapply mf_cnt_next; [exact HNE | exact RF | lia].
  - rewrite RC2. lia.
Qed.

Lemma ha_ref_144c0 : m_refuse_contract -> forall n, H_MF_TAIL n ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    m_file_regs c (mf_next p rest) (line + 1) s0 s1 s2 s3 (Z_to_bv 64 9) s8 s9 s10 s11 ->
    evt rsegs
      (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (m_refuse mc (line + 1) false, None) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x144c0) fc None m (seg_rom rsegs)).
Proof.
  intros HMR n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest HL HNE HLOOP HREGS.
  apply mf_loop_iff in HLOOP. destruct HLOOP as (CTX & TXT & ST).
  destruct ST as (MC & CUR & CUROK & K0 & L0 & LB & RF & OV).
  assert (LR : (1 <= length rest)%nat) by (destruct rest; [congruence | cbn [length]; lia]).
  pose proof CTX as B. apply mf_ctx_bounds in B. destruct B as (IMG & LOS & SP63 & SP016 & SP16 & _ & C0 & CE).
  pose proof CTX as (ESP & _).
  pose proof HREGS as (Er0 & Er1 & Er2 & Er3 & _). subst s0 s3.
  (* 0x144c0 a0 = c; 0x144c4 a1 = line + 1; 0x144c8 jal m_refuse *)
  step. step. step.
  eapply (mf_refuse_call HMR 0x144c8) with (knock := false) (mc := mc);
    [lia | lia | reflexivity | exact CTX | exact TXT | exact CUR | exact MC | lia | lia | ].
  intros m1 F1 fc1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 CTX1 TXT1 CUR1 MC1 MU1 WM1 HF1.
  eapply mf_post_back; [exact HF1 | exact MU1 | exact WM1 | |].
  { apply (sub_fp_trans _ (M_FILE_W (bv_unsigned sp0) c k0 (m_refuse mc (line + 1) false))).
    - apply mf_W_refuse; unfold M_FILE_STACK, M_REFUSE_STACK, M_FILE_FRAME in *; [lia | lia | exact K0].
    - apply (mf_W_fin _ _ _ (m_refuse mc (line + 1) false, None)). exact I. }
  replace (0x144c8 + 4) with 0x144cc by reflexivity.
  destruct (ha_null_facts m1 fc1 (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
              p rest (m_refuse mc (line + 1) false) false CTX1 TXT1 MC1) as (SO & NF).
  (* 0x144cc sd zero, 0x20(sp) *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bb) _) =>
    replace (write_to_mem mm aa bb) with (write_to_mem m1 (wa (bv_unsigned sp + 32)) (le8 (Z_to_bv 64 0)))
      by (f_equal; first [reflexivity | unfold wa; word_eq_tac])
  end.
  remember (write_to_mem m1 (wa (bv_unsigned sp + 32)) (le8 (Z_to_bv 64 0))) as m2 eqn:Em2.
  destruct (NF m2 eq_refl) as (CTX2 & TXT2 & MC2 & CUR2 & MU2 & WM2). clear Em2 NF.
  eapply mf_post_back; [intros k Hk; reflexivity | exact MU2 | exact WM2
                       | apply mf_W_frame; unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *; lia | ].
  (* 0x144d0 j 0x14598; 0x14598 s7 = 9; 0x1459c j 0x143d4 *)
  step. step. step.
  pose proof (m_refuse_sizes mc (line + 1) false) as (_ & SZ).
  pose proof (ha_refuse_cnt mc (line + 1) false) as (RC1 & RC2).
  pose proof (mf_rest_lt rest HNE) as RLT.
  eapply (ha_at_tail n HT); [exact HL | exact HNE | exact CTX2 | exact TXT2 | exact MC2 | exact CUR2 | exact I
                            | lia | lia | lia | | | exact HREGS].
  - eapply mf_cnt_next; [exact HNE | exact RF | lia].
  - rewrite RC2. lia.
Qed.

(** ** The piece: HDR 0x14188 -> HFIND 0x14488, or the tail through a refusal *)
Lemma mf_hdra_holds : memchr_contract -> ieq_contract -> m_refuse_contract -> S_MF_HDRA.
Proof.
  intros HMC HIQ HMR n HT HHF. unfold memchr_contract in HMC. unfold ieq_contract in HIQ.
  unfold H_MF_HFIND in HHF. unfold H_MF_HDR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest i j
    HL HNE HLOOP HREGS HLEN Hij HjL HSL HLBR E5 E6 E2.
  rewrite <- HSL. unfold MF_PC_HDR.
  (* the context *)
  pose proof HLOOP as HL0. apply mf_loop_iff in HL0. destruct HL0 as (CTX & TXT & _).
  pose proof TXT as T. apply mf_text_props in T. destruct T as (NZ & RNG & P0 & PEND & SPAN).
  destruct (ha_line_props rest RNG) as [LL LRNG].
  pose proof CTX as B. apply mf_ctx_bounds in B. destruct B as (IMG & LOS & SP63 & SP016 & SP16 & _ & C0 & CE).
  pose proof CTX as (ESP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  assert (PL : p + Z.of_nat (length rest) + 1 <= 2 ^ 64).
  { unfold cstr_span in PEND. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)). lia. }
  change (sa_img_end SA) with 0x536e8 in IMG.
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in LOS, ESP.
  pose proof HREGS as (Er0 & Er1 & Er2 & Er3 & Er7 & Er8 & Er9 & Er10 & Er11).
  subst s0 s1 s2 s3 s7 s8 s9 s10 s11 s5 s6 a2.
  unfold BLANK_MASK.
  assert (SLEN : length (slice i j (mf_line rest)) = (j - i)%nat) by (apply slice_length; lia).
  assert (SRNG : Forall (fun x => 0 <= x < 256) (slice i j (mf_line rest))) by (apply ha_forall_slice; exact LRNG).
  assert (S0 : nth 0 (slice i j (mf_line rest)) 0 = 91).
  { rewrite slice_nth by lia. rewrite Nat.add_0_r. exact HLBR. }
  (* 0x14188 a1 = ']'; 0x1418c a0 = s; 0x14190 jal memchr *)
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HMC with (buf := zb (slice i j (mf_line rest))); rewrite ?unsigned_lit by lia.
    - apply (ha_bytes_slice m (bv_unsigned sp0) lo c p rest i j TXT). lia.
    - apply ha_memchr_ok. unfold zb. rewrite length_map, SLEN. lia.
    - exact MI. }
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU1 & WM1
              & MI1 & _).
  apply ha_munch_nil in MU1. subst m1. clear WM1 MI1.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (unsigned_lit (p + Z.of_nat i)) by lia.
  rewrite (unsigned_lit (Z.of_nat (j - i))) by lia.
  change (bv_unsigned (Z_to_bv 64 93) mod 256) with 93.
  rewrite (ha_memchr_res (p + Z.of_nat i) 93 (Z.of_nat (j - i)) (slice i j (mf_line rest)) SRNG)
    by (rewrite SLEN; reflexivity).
  destruct (memchr (slice i j (mf_line rest)) 93) as [ci|] eqn:MCH.
  2: { (* 0x14194: no ']', to 0x1463c *)
       zstep. if_cases Hc; zify_cond Hc; [|exfalso; lia].
       assert (MH : m_header mc (slice i j (mf_line rest)) (line + 1) = (m_refuse mc (line + 1) false, None))
         by (unfold m_header; rewrite MCH; reflexivity).
       rewrite MH. eapply (ha_ref_1463c HMR n HT); eassumption. }
  destruct (memchr_some _ _ _ MCH) as (Hci & Hcv & Hcmin).
  rewrite SLEN in Hci.
  assert (Hci1 : (1 <= ci)%nat) by (destruct ci; [rewrite S0 in Hcv; lia | lia]).
  zstep. if_cases Hc; zify_cond Hc; [exfalso; lia|].
  (* 0x14198 s4 = close; 0x1419c a0 = close + 1; 0x141a0 bne a0, s6 *)
  zstep. zstep. zstep. if_cases Hc2; zify_cond Hc2.
  { assert (MH : m_header mc (slice i j (mf_line rest)) (line + 1) = (m_refuse mc (line + 1) false, None)).
    { apply m_header_refuse. intros ci' MC' S' _ _ _. rewrite MCH in MC'. injection MC' as <-.
      exfalso. rewrite SLEN in S'. lia. }
    rewrite MH. eapply (ha_ref_1463c HMR n HT); eassumption. }
  assert (Eci : S ci = (j - i)%nat) by lia.
  assert (HU : slice 1 ci (slice i j (mf_line rest)) = slice (i + 1) (i + ci) (mf_line rest))
    by (apply slice_slice; lia).
  assert (LU : length (slice (i + 1) (i + ci) (mf_line rest)) = (ci - 1)%nat)
    by (rewrite slice_length by lia; lia).
  (* 0x141a4-0x141fc: the strip of [s + 1, close) *)
  eapply ha_strip1 with (u := slice (i + 1) (i + ci) (mf_line rest)) (A := p + Z.of_nat (i + 1)).
  { apply ha_nth_range, ha_forall_slice, LRNG. }
  { intros q Hq. rewrite LU in Hq. apply (ha_rd_slice m (bv_unsigned sp0) lo c p rest (i + 1) (i + ci) TXT); lia. }
  { lia. }
  { rewrite LU. lia. }
  { word_eq_tac. }
  { rewrite LU. word_eq_tac. }
  intros fb be a0' w4 w6 Hfbe HS E4 E6. rewrite LU in Hfbe. subst w4 w6.
  (* 0x143e4 s7 = be - b; 0x143e8 a0 = 8; 0x143ec blt s7, a0 *)
  zstep. zstep. zstep. if_cases Hc3; zify_cond Hc3; rewrite ?ha_signed_small in Hc3 by lia.
  { assert (MH : m_header mc (slice i j (mf_line rest)) (line + 1) = (m_refuse mc (line + 1) false, None)).
    { apply m_header_refuse. intros ci' MC' _ L8 _ _. rewrite MCH in MC'. injection MC' as <-.
      rewrite HU, HS, slice_length in L8 by lia. exfalso. lia. }
    rewrite MH. eapply (ha_ref_144c0 HMR n HT); eassumption. }
  assert (Hb8 : (8 <= be - fb)%nat) by lia.
  (* 0x143f0-0x14400: a2 = "segment", a1 = 7, a0 = b, jal ieq *)
  zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HIQ with (l := zb (slice (i + 1 + fb) (i + 1 + fb + 7) (mf_line rest))) (w := S_segment) (lo := lo).
    unfold ieq_pre. rewrite !unsigned_lit by lia.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
    - lia.
    - replace (p + Z.of_nat (i + 1) + Z.of_nat fb) with (p + Z.of_nat (i + 1 + fb)) by lia.
      apply (ha_bytes_slice m (bv_unsigned sp0) lo c p rest); [exact TXT | lia].
    - unfold zb. rewrite length_map, slice_length by lia. lia.
    - replace (p + Z.of_nat (i + 1) + Z.of_nat fb) with (p + Z.of_nat (i + 1 + fb)) by lia.
      apply (ha_text_apart m (bv_unsigned sp0) lo c p rest (i + 1 + fb) 7 (bv_unsigned sp) TXT); lia.
    - lia.
    - apply ha_seg_lit. exact MI.
    - unfold apart. left. change (Z.of_nat (length S_segment)) with 7. lia.
    - apply (ha_ctx_stack m fc (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11);
        [exact CTX | unfold IEQ_STACK, M_FILE_STACK, M_FILE_FRAME, PRINTF_K; lia].
    - exact MI. }
  intros ms' (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m1 & -> & MU1 & WM1
              & MI1 & STK1 & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  pose proof (ha_loop_ieq m m1 fc _ _ lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
                HLOOP MU1 WM1 MI1 STK1) as HLOOP1.
  eapply mf_post_back; [intros k Hk; reflexivity | exact MU1 | exact WM1
                       | apply mf_W_frame; unfold IEQ_STACK, M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *; lia | ].
  pose proof HLOOP1 as HL1. apply mf_loop_iff in HL1. destruct HL1 as (CTX1 & TXT1 & _).
  rewrite (ha_zs_zb (slice (i + 1 + fb) (i + 1 + fb + 7) (mf_line rest)) (ha_forall_slice _ _ _ _ LRNG)).
  assert (HB7 : firstn 7 (slice fb be (slice (i + 1) (i + ci) (mf_line rest))) =
                slice (i + 1 + fb) (i + 1 + fb + 7) (mf_line rest)).
  { rewrite slice_slice by lia. apply ha_firstn_slice. lia. }
  assert (HC7 : nth 7 (slice fb be (slice (i + 1) (i + ci) (mf_line rest))) 0 = nth (i + 1 + fb + 7) rest 0).
  { rewrite slice_slice by lia. rewrite slice_nth by lia. rewrite <- (mf_line_nth rest) by lia. f_equal; lia. }
  assert (RC7 : 0 <= nth (i + 1 + fb + 7) rest 0 < 256) by (apply ha_nth_range; exact RNG).
  pose proof (mf_text_byte m1 (bv_unsigned sp0) lo c p rest (i + 1 + fb + 7) TXT1 ltac:(lia)) as RD7.
  destruct (ieq (slice (i + 1 + fb) (i + 1 + fb + 7) (mf_line rest)) S_segment) eqn:IQ; cbn [b2z].
  2: { (* 0x14404: not "segment", to 0x144c0 *)
       zstep. if_cases Hc4; zify_cond Hc4; [|exfalso; lia].
       assert (MH : m_header mc (slice i j (mf_line rest)) (line + 1) = (m_refuse mc (line + 1) false, None)).
       { apply m_header_refuse. intros ci' MC' _ _ IQ' _. rewrite MCH in MC'. injection MC' as <-.
         rewrite HU, HS, HB7, IQ in IQ'. discriminate. }
       rewrite MH. eapply (ha_ref_144c0 HMR n HT); eassumption. }
  zstep. if_cases Hc4; zify_cond Hc4; [exfalso; lia|].
  (* 0x14408 a0 = b[7] *)
  zstep.
  lazymatch goal with |- evt _ ?QQ (MS ?R ?FF _ ?fcc ?rvv ?mm ?roo) =>
    assert (STRIP2 : sp_tab (nth (i + 1 + fb + 7) rest 0) = true ->
                     evt rsegs QQ (MS R FF (Z_to_bv 64 0x14414) fcc rvv mm roo))
  end.
  2: { (* 0x1440c b[7] = '\t'; 0x14410 b[7] <> ' ' to 0x144c0 *)
       zstep. if_cases Hc5; zify_cond Hc5; rewrite ?ha_u8 in Hc5 by exact RC7.
       - apply STRIP2. unfold sp_tab. rewrite Hc5. reflexivity.
       - zstep. if_cases Hc6; zify_cond Hc6; rewrite ?ha_u8 in Hc6 by exact RC7.
         + assert (MH : m_header mc (slice i j (mf_line rest)) (line + 1) = (m_refuse mc (line + 1) false, None)).
           { apply m_header_refuse. intros ci' MC' _ _ _ SPT. rewrite MCH in MC'. injection MC' as <-.
             rewrite HU, HS, HC7 in SPT. unfold sp_tab in SPT. apply orb_true_iff in SPT.
             destruct SPT as [SPT|SPT]; apply Z.eqb_eq in SPT; lia. }
           rewrite MH. eapply (ha_ref_144c0 HMR n HT); eassumption.
         + apply STRIP2. unfold sp_tab. rewrite Hc6. reflexivity. }
  intros SPT.
  (* 0x14414-0x14474: the strip of [b + 7, be) *)
  assert (HSK : skipn 7 (slice fb be (slice (i + 1) (i + ci) (mf_line rest))) =
                slice (i + 1 + fb + 7) (i + 1 + be) (mf_line rest)).
  { rewrite slice_slice by lia. rewrite ha_skipn_slice by lia. reflexivity. }
  assert (LU2 : length (slice (i + 1 + fb + 7) (i + 1 + be) (mf_line rest)) = (be - fb - 7)%nat)
    by (rewrite slice_length by lia; lia).
  eapply ha_strip2 with (u := slice (i + 1 + fb + 7) (i + 1 + be) (mf_line rest)) (A := p + Z.of_nat (i + 1 + fb + 7)).
  { apply ha_nth_range, ha_forall_slice, LRNG. }
  { intros q Hq. rewrite LU2 in Hq.
    apply (ha_rd_slice m1 (bv_unsigned sp0) lo c p rest (i + 1 + fb + 7) (i + 1 + be) TXT1); lia. }
  { lia. }
  { rewrite LU2. lia. }
  { lia. }
  { rewrite LU2. lia. }
  { word_eq_tac. }
  { rewrite LU2. word_eq_tac. }
  { rewrite LU2. word_eq_tac. }
  intros fb2 be2 a0'' a1'' w4 w5 w6 Hfbe2 HS2 E4' E5'. rewrite LU2 in Hfbe2. subst w4 w5.
  assert (LN : length (slice fb2 be2 (slice (i + 1 + fb + 7) (i + 1 + be) (mf_line rest))) = (be2 - fb2)%nat)
    by (apply slice_length; lia).
  (* 0x14478 beq s4, s5: an empty name *)
  zstep. if_cases Hc7; zify_cond Hc7.
  { assert (MH : m_header mc (slice i j (mf_line rest)) (line + 1) = (m_refuse mc (line + 1) false, None)).
    { apply m_header_refuse. intros ci' MC' _ _ _ _. rewrite MCH in MC'. injection MC' as <-.
      rewrite HU, HS, HSK, HS2, LN. left. lia. }
    rewrite MH. eapply (ha_ref_1463c HMR n HT); eassumption. }
  (* 0x1447c s6 = n; 0x14480 a0 = 16; 0x14484 bgeu s6, a0: 16 bytes or more *)
  zstep. zstep. zstep. if_cases Hc8; zify_cond Hc8.
  { assert (MH : m_header mc (slice i j (mf_line rest)) (line + 1) = (m_refuse mc (line + 1) false, None)).
    { apply m_header_refuse. intros ci' MC' _ _ _ _. rewrite MCH in MC'. injection MC' as <-.
      rewrite HU, HS, HSK, HS2, LN. right. lia. }
    rewrite MH. eapply (ha_ref_1463c HMR n HT); eassumption. }
  (* 0x14488: HFIND *)
  assert (MH : m_header mc (slice i j (mf_line rest)) (line + 1) =
               mh_find mc (slice fb2 be2 (slice (i + 1 + fb + 7) (i + 1 + be) (mf_line rest))) (line + 1)).
  { rewrite (m_header_find mc _ (line + 1) ci MCH).
    - rewrite HU, HS, HSK, HS2. reflexivity.
    - rewrite SLEN. lia.
    - rewrite HU, HS, slice_length by lia. lia.
    - rewrite HU, HS, HB7. exact IQ.
    - rewrite HU, HS, HC7. exact SPT.
    - rewrite HU, HS, HSK, HS2, LN. lia. }
  rewrite MH.
  eapply HHF with (o := (i + 1 + fb + 7 + fb2)%nat)
                  (nm := slice fb2 be2 (slice (i + 1 + fb + 7) (i + 1 + be) (mf_line rest))).
  { exact HL. }
  { exact HNE. }
  { exact HLOOP1. }
  { exact HREGS. }
  { rewrite LN. lia. }
  { rewrite LN. lia. }
  { rewrite LN. rewrite mf_line_firstn by lia. rewrite slice_slice by lia. f_equal; lia. }
  { word_eq_tac. }
  { rewrite LN. word_eq_tac. }
Qed.
