From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes check_as_written_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require FrameAPI.
Import ListNotations.
Local Open Scope Z_scope.
Local Abbreviation alloc_ceiling := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling.

Lemma caw_vm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma caw_vm_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma caw_k_val : CAW_K = 13760.
Proof. reflexivity. Qed.

Lemma caw_nodup_fst : forall {X Y : Type} (l : list (X * Y)) x y y', List.NoDup (map fst l) -> In (x, y) l ->
  In (x, y') l -> y = y'.
Proof.
  intros X Y l. induction l as [|[a b] l IH]; intros x y y' ND H1 H2; [destruct H1|].
  cbn [map fst] in ND. inversion ND as [|? ? Hn ND']; subst.
  destruct H1 as [E1|H1], H2 as [E2|H2].
  - inversion E1; inversion E2; subst. reflexivity.
  - inversion E1; subst. exfalso. apply Hn. apply in_map_iff. exists (x, y'). split; [reflexivity | exact H2].
  - inversion E2; subst. exfalso. apply Hn. apply in_map_iff. exists (x, y). split; [reflexivity | exact H1].
  - exact (IH x y y' ND' H1 H2).
Qed.

Lemma caw_pairwise_mid : forall {T : Type} (R : T -> T -> Prop) b1 z b2, pairwise R (b1 ++ z :: b2) ->
  forall y, In y (b1 ++ b2) -> R z y \/ R y z.
Proof.
  intros T R b1. induction b1 as [|x b1 IH]; intros z b2 H y Hy; cbn in *.
  - destruct H as [H _]. left. apply H. exact Hy.
  - destruct H as [H1 H2]. destruct Hy as [<-|Hy].
    + right. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH z b2 H2 y Hy).
Qed.

Lemma caw_mid_unique : forall {T : Type} (b1 b2 c1 c2 : list T) z, b1 ++ z :: b2 = c1 ++ z :: c2 ->
  ~ In z b1 -> ~ In z b2 -> b1 = c1 /\ b2 = c2.
Proof.
  intros T b1. induction b1 as [|x b1 IH]; intros b2 c1 c2 z E N1 N2; destruct c1 as [|y c1]; cbn in E.
  - injection E as E. split; [reflexivity | exact E].
  - injection E as E1 E2. subst y. exfalso. apply N2. rewrite E2. apply in_or_app. right. left. reflexivity.
  - injection E as E1 E2. subst x. exfalso. apply N1. left. reflexivity.
  - injection E as E1 E2. subst y. destruct (IH b2 c1 c2 z E2 (fun h => N1 (or_intror h)) N2) as [-> ->].
    split; reflexivity.
Qed.

Lemma caw_resv : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs) =
  [(65536, 12288); (77824, 65536); (143360, 4096); (147456, 204800)].
Proof. vm_compute. reflexivity. Qed.

Lemma caw_find_ro : forall (segs : list Segment) lo hi a,
  forallb (fun s => seg_writable s || ((lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi)))
    segs = true ->
  a < lo \/ hi <= a ->
  match find_segment segs a 1 with Some sg => negb (seg_writable sg) | None => false end = false.
Proof.
  induction segs as [|s segs IH]; intros lo hi a H Ha; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  destruct ((Z.of_N (seg_base s) <=? a) && (a + 1 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    destruct (seg_writable s) eqn:W; [reflexivity|]. cbn in H1.
    apply andb_prop in H1 as [H3 H4]. apply Z.leb_le in H3. apply Z.leb_le in H4. lia.
  - exact (IH lo hi a H2 Ha).
Qed.

Lemma caw_rsegs_ro :
  forallb (fun s => seg_writable s || ((0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x23000)))
    rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma caw_ro_out : forall a, 0 <= a < 2 ^ 64 -> a < 0x10000 \/ 0x23000 <= a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hout. unfold ro_addr. rewrite unsigned_lit by lia.
  exact (caw_find_ro rsegs 0x10000 0x23000 a caw_rsegs_ro Hout).
Qed.

Lemma caw_keep : forall a, 0 <= a < 2 ^ 47 -> a < 0x10000 \/ 0x23000 <= a -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.cj_drop rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hout. apply OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.cj_drop_false_intro; [apply caw_ro_out; lia|].
  right. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia.
Qed.

Lemma caw_ms_rel_cj : forall s R F pc fc rv m0 ro, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.ms_rel_cj rsegs s (MS R F pc fc rv m0 ro) ->
  exists m', s = MS R F pc fc rv m' ro /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.mem_rel_cj rsegs m' m0.
Proof.
  intros [r f p sv rv' c mm o] R F pc fc rv m0 ro H. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.ms_rel_cj, MS in H. cbn in H.
  destruct H as (-> & -> & -> & -> & -> & -> & -> & H). exists mm. split; [reflexivity | exact H].
Qed.

Lemma caw_rw_rel_cj : forall m m0 A cs, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.mem_rel_cj rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.bytes_at_rel_cj rsegs m m0 A _ HR Hb).
  - exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.wr_at_rel_cj rsegs m m0 A _ HR Hw).
Qed.

Lemma caw_rw_norm_cj : forall m A cs, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.ro_agree rsegs m -> rw_cells rsegs m A cs ->
  A + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.cj_drop rsegs (Z_to_bv 64 (A + i)) = false) ->
  rw_cells rsegs (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.normalize_cj rsegs m) A cs.
Proof.
  intros m A cs RO ((Hwf & Hb) & Hw) Ht Hk. split; [split; [exact Hwf|]|].
  - apply OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.bytes_at_normalize_cj_low; [exact RO | | exact Hb].
    rewrite cells_bytes_length by exact Hwf. exact Ht.
  - exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.wr_at_norm_cj rsegs m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.normalize_cj rsegs m) A _
             (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.mem_rel_cj_normalize rsegs m RO) Hw Hk).
Qed.

Lemma caw_stk_norm_cj : forall m lo hi, stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.cj_drop rsegs (Z_to_bv 64 a) = false) ->
  stk rsegs (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (N : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.normalize_cj rsegs m (wa a) = m (wa a))
    by (unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.normalize_cj, wa; rewrite Hk by exact Ha; reflexivity).
  destruct (H a Ha) as [W [b E]]. split.
  - unfold wview in *. rewrite N. exact W.
  - exists b. unfold mrd in *. rewrite N. exact E.
Qed.

Lemma caw_le_back : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  assert (Hn : 0 <= bytes_le_to_Z bs).
  { clear IH. induction bs as [|b' bs' IH']; cbn [bytes_le_to_Z]; [lia|].
    apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; exact IH']. }
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  rewrite (lor_shiftl8_add (bv_unsigned b) (bytes_le_to_Z bs)) by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. exact IH.
Qed.

Lemma caw_stk_C4 : forall m a, stk rsegs m a (a + 4) -> exists w, rw_cells rsegs m a [C4 w].
Proof.
  intros m a ST. destruct (stk_bytes rsegs m a (a + 4) ST ltac:(lia)) as (bs & L & Bs).
  replace (Z.to_nat (a + 4 - a)) with 4%nat in L by lia.
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le4. rewrite unsigned_lit_wrap.
    rewrite (Z_to_le_bytes_mod 4 (bytes_le_to_Z bs) 64) by lia. rewrite <- L. rewrite caw_le_back. exact Bs.
  - cbn [cells_size csize]. destruct ST as (S1 & S2 & S3). split; [lia|]. split; [lia|].
    intros i Hi. apply (S3 (a + i)). lia.
Qed.

Lemma caw_wview_none : forall m (x : word), m x = None -> wview rsegs m x = wview rsegs (fun _ => None) x.
Proof. intros m x E. unfold wview. rewrite E. reflexivity. Qed.

Lemma caw_img_stk : forall m a n,
  forallb (fun i => match wview rsegs (fun _ => None) (Z_to_bv 64 (a + Z.of_nat i)),
                          mrd rsegs (fun _ => None) (Z_to_bv 64 (a + Z.of_nat i)) with
                    | Some _, Some _ => true | _, _ => false end) (seq 0 n) = true ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> stk rsegs m a (a + Z.of_nat n).
Proof.
  intros m a n H Ha Hn. split; [exact Ha|]. split; [exact Hn|]. intros x Hx.
  rewrite forallb_forall in H. specialize (H (Z.to_nat (x - a))).
  rewrite in_seq in H. specialize (H ltac:(lia)). rewrite Z2Nat.id in H by lia.
  replace (a + (x - a)) with x in H by lia. unfold wa.
  destruct (m (Z_to_bv 64 x)) as [b|] eqn:E.
  - split; [unfold wview; rewrite E; discriminate|]. exists b. unfold mrd. rewrite E. reflexivity.
  - rewrite (caw_wview_none m _ E).
    assert (M : mrd rsegs m (Z_to_bv 64 x) = mrd rsegs (fun _ => None) (Z_to_bv 64 x)) by (unfold mrd; rewrite E; reflexivity).
    rewrite M.
    destruct (wview rsegs (fun _ => None) (Z_to_bv 64 x)); [|discriminate].
    destruct (mrd rsegs (fun _ => None) (Z_to_bv 64 x)) as [c|]; [|discriminate].
    split; [discriminate | exists c; reflexivity].
Qed.

Lemma caw_got_stk : forall m, stk rsegs m OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GOT_GUARD (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GOT_GUARD + Z.of_nat 8).
Proof. intros m. apply caw_img_stk; [vm_compute; reflexivity | unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GOT_GUARD; lia | unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GOT_GUARD; lia]. Qed.

Lemma caw_guard_stk : forall m, stk rsegs m OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GUARD (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GUARD + Z.of_nat 8).
Proof. intros m. apply caw_img_stk; [vm_compute; reflexivity | unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GUARD; lia | unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GUARD; lia]. Qed.

Lemma caw_errno_stk : forall m, stk rsegs m OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO + Z.of_nat 4).
Proof. intros m. apply caw_img_stk; [vm_compute; reflexivity | unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO; lia | unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO; lia]. Qed.

Section G.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Local Abbreviation segs := (ms_segs B).
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.
Hypothesis ERU : errno_unowned B API.
Hypothesis HERR : errno_addr B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO.

Lemma caw_img_iff : forall a, in_img B a <-> 0x10000 <= a < 0x56000.
Proof using HS.
  intros a. split.
  - intros [_ (s & Hin & H)]. rewrite HS in Hin.
    apply (in_map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s)))) in Hin. rewrite caw_resv in Hin.
    cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
  - intros Ha. split; [rewrite HS; discriminate|].
    assert (P : exists lo len, In (lo, len) [(65536, 12288); (77824, 65536); (143360, 4096); (147456, 204800)] /\
                  lo <= a < lo + len).
    { destruct (Z_lt_ge_dec a 77824); [exists 65536, 12288; split; [left; reflexivity | lia]|].
      destruct (Z_lt_ge_dec a 143360); [exists 77824, 65536; split; [right; left; reflexivity | lia]|].
      destruct (Z_lt_ge_dec a 147456); [exists 143360, 4096; split; [right; right; left; reflexivity | lia]|].
      exists 147456, 204800. split; [right; right; right; left; reflexivity | lia]. }
    destruct P as (lo & len & Hin & Hr). rewrite <- caw_resv in Hin. apply in_map_iff in Hin.
    destruct Hin as (s & Es & Hs). injection Es as E1 E2. exists s. rewrite HS. split; [exact Hs | lia].
Qed.

Lemma caw_errno_img : forall a, errno_addr B <= a < errno_addr B + 4 -> in_img B a.
Proof using HS HERR.
  intros a Ha. apply caw_img_iff. rewrite HERR in Ha. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO in Ha. lia.
Qed.

Lemma caw_img_low : img_low B.
Proof using HS.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite HS. vm_compute. reflexivity.
  - pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value. lia.
Qed.

Lemma caw_in_blocks : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k H. unfold blocks in H. apply in_map_iff in H as ([p k'] & E & Hin). cbn in E.
  inversion E; subst. exists p. split; [exact Hin | reflexivity].
Qed.

Lemma caw_ub_blocks : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. apply in_map_iff. exists (p, k). split; [reflexivity | exact H]. Qed.

Lemma caw_block_facts : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  present mem (a + i) /\ 4096 <= a /\ a + k <= alloc_ceiling /\ ~ owned B L A (a + i) /\ ~ in_img B (a + i).
Proof using AX.
  intros L A mem md a k i HM Hin Hi. destruct (caw_in_blocks L A a k Hin) as (p & Hp & <-).
  destruct (mr_blocks _ _ (aa_laws API) L A mem md p k i HM Hp Hi) as (H1 & H2 & H3 & H4).
  repeat split; try assumption. exact (ax_blocks_img AX L A mem md p k i HM Hp Hi).
Qed.

Lemma caw_block_range : forall L A mem md a k, MR L A mem md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros L A mem md a k HM Hin. destruct (caw_in_blocks L A a k Hin) as (p & Hp & <-).
  exact (mr_blocks_range _ _ (aa_laws API) L A mem md p k HM Hp).
Qed.

Lemma caw_pairwise_in : forall {T : Type} (R : T -> T -> Prop) l x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros T R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
  destruct HP as [Hz HP]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - congruence.
  - left. apply Hz. exact Hy.
  - right. apply Hz. exact Hx.
  - apply IH; assumption.
Qed.

Lemma caw_blocks_sep : forall L A m md x y, MR L A m md -> In x (blocks L A) -> In y (blocks L A) -> x <> y ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros L A m md x y HM Hx Hy Hne.
  destruct (caw_pairwise_in _ _ x y (mr_blocks_disjoint _ _ (aa_laws API) L A m md HM) Hx Hy Hne) as [H|H];
    unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YO0f.ranges_disjoint in H; lia.
Qed.

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE0 : call_pre_k B MR CAW_K L0 A0 regs0 mem0 md0.

Definition cj (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
  MR L A mem md /\ WF A /\ bounded A /\ layout_le A0 L0 L /\
  (st_init_done A0 = true -> st_init_done A = true) /\
  (st_init_done A = false -> forall i, 0 <= i < 8 ->
     mbyte segs mem (ms_libc B + 8 + i) = mbyte segs mem0 (ms_libc B + 8 + i)) /\
  (length (st_regions A0) <= length (st_regions A))%nat /\
  (forall p n, In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A) /\ ptr_addr L p = ptr_addr L0 p) /\
  (exists vm, md = with_vmmaps vm md0) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B CAW_K regs0 a ->
     mbyte segs mem a = mbyte segs mem0 a /\ (writable_at segs mem0 a <-> writable_at segs mem a)) /\
  (forall a, in_img B a -> (forall L1 A1 m1 md1, MR L1 A1 m1 md1 -> ~ owned B L1 A1 a) ->
     ~ scratch_k B CAW_K regs0 a ->
     mbyte segs mem a = mbyte segs mem0 a /\ (writable_at segs mem0 a <-> writable_at segs mem a)) /\
  (forall p n i, In (p, n) (user_blocks A0) -> 0 <= i < n ->
     mbyte segs mem (ptr_addr L0 p + i) = mbyte segs mem0 (ptr_addr L0 p + i)) /\
  (forall a, scratch_k B CAW_K regs0 a -> writable_at segs mem a) /\
  ro_agree segs mem.

Lemma cj_init : ro_agree segs mem0 -> cj L0 A0 mem0 md0.
Proof using PRE0.
  intros RA. destruct PRE0 as (HM & HWF & HBD & _ & _ & _ & _ & HW & _ & HER & _).
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|].
  split; [tauto|]. split; [intros; reflexivity|]. split; [lia|].
  split; [intros p n H; split; [exact H | reflexivity]|].
  split; [exists (m_vmmaps md0); apply caw_vm_self|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|].
  split; [intros a [Ha|Ha]; [apply HW | apply HER]; exact Ha|].
  exact RA.
Qed.

Lemma cj_final : forall L A mem md regs',
  cj L A mem md -> regs_preserved regs0 regs' ->
  rpost B API CAW_K L0 A0 regs0 mem0 md0 (fun _ => False) (fun _ _ => False) L A regs' mem md.
Proof.
  intros L A mem md regs' (HM & HWF & HBD & HLY & HI & HLB & HLN & HUB & HMD & HHI & HIM & HB0 & HSC & HRA) RP.
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HLY|].
  split; [exact HI|]. split; [exact HLB|]. split; [exact HLN|].
  split; [intros p n H _; exact (proj1 (HUB p n H))|].
  split; [intros p n H _; exact (proj2 (HUB p n H))|].
  split; [exact RP|]. split; [exact HMD|].
  split; [intros a Ha Hsc _; exact (HHI a Ha Hsc)|].
  split; [intros a Ha Hno Hsc _; exact (HIM a Ha Hno Hsc)|].
  split; [intros p n i H _ Hi _; exact (HB0 p n i H Hi)|].
  exact HSC.
Qed.

Lemma cj_blocks0 : forall L A mem md a k, cj L A mem md -> In (a, k) (blocks L0 A0) -> In (a, k) (blocks L A).
Proof.
  intros L A mem md a k J Hin. destruct J as (_ & _ & _ & _ & _ & _ & _ & HUB & _).
  destruct (caw_in_blocks L0 A0 a k Hin) as (p & Hp & <-). destruct (HUB p k Hp) as [H1 H2].
  rewrite <- H2. apply caw_ub_blocks. exact H1.
Qed.

Lemma cj_mem0 : forall L A mem md a k i, cj L A mem md -> In (a, k) (blocks L0 A0) -> 0 <= i < k ->
  mbyte segs mem (a + i) = mbyte segs mem0 (a + i).
Proof.
  intros L A mem md a k i J Hin Hi. pose proof J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB0 & _).
  destruct (caw_in_blocks L0 A0 a k Hin) as (p & Hp & <-). exact (HB0 p k i Hp Hi).
Qed.

Lemma cj_kindA : forall L A mem md mem' W,
  cj L A mem md -> Frame.munch W mem mem' -> Frame.wmono segs mem mem' -> ro_agree segs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> (spZ regs0 - CAW_K <= x < spZ regs0) \/
     (errno_addr B <= x < errno_addr B + 4) \/
     (exists r k, In (r, k) (blocks L A) /\ ~ In (r, k) (blocks L0 A0) /\ r <= x < r + k /\ present mem' x)) ->
  cj L A mem' md.
Proof using HS AX ERU HERR PRE0.
  intros L A mem md mem' W J MU WM RA' CLS.
  pose proof J as (HM & HWF & HBD & HLY & HI & HLB & HLN & HUB & HMD & HHI & HIM & HB0 & HSC & HRA).
  pose proof PRE0 as (HM0 & _ & _ & _ & _ & HK & HK63 & _).
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hac. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as Hacv.
  pose proof caw_k_val as HKv.
  assert (OUT : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs0 - CAW_K <= x < spZ regs0) ->
            ~ (errno_addr B <= x < errno_addr B + 4) ->
            (forall r k, In (r, k) (blocks L A) -> ~ In (r, k) (blocks L0 A0) -> ~ (r <= x < r + k)) ->
            Frame.outside W x).
  { intros x Hx H1 He H2. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|].
    exfalso. destruct (CLS x Hx Ho) as [H|[H|(r & k & Hr & Hr0 & Hrx & _)]];
      [exact (H1 H) | exact (He H) | exact (H2 r k Hr Hr0 Hrx)]. }
  assert (OWN : forall a, owned B L A a -> 0 <= a < alloc_ceiling /\ Frame.outside W a).
  { intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md a HM Ho) as Hl. split; [exact Hl|].
    apply OUT; [lia | lia | intros He; exact (ERU L A mem md a HM He Ho) |]. intros r k Hr _ Hrx.
    destruct (caw_block_facts L A mem md r k (a - r) HM Hr ltac:(lia)) as (_ & _ & _ & Hno & _).
    replace (r + (a - r)) with a in Hno by lia. exact (Hno Ho). }
  split.
  { destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & Hm).
    eapply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
    - intros a Ho. destruct (OWN a Ho) as [Hl0 Hout]. apply (mbyte_munch _ W); [exact MU | lia | exact Hout].
    - intros a Ho Hp. destruct (OWN a Ho) as [Hl0 Hout]. apply (present_munch W mem); [exact MU | lia | exact Hout | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) L A mem md p n i HM Hin Hi) as (Hp & H1 & H2 & _).
      destruct (kb_outside_dec W (ptr_addr L p + i)) as [Ho|Ho].
      + apply (present_munch W mem); [exact MU | lia | exact Ho | exact Hp].
      + destruct (CLS (ptr_addr L p + i) ltac:(lia) Ho) as [Hst | [He | (r & k & _ & _ & _ & Hpr)]];
          [lia | | exact Hpr].
        exfalso. pose proof (ax_blocks_img AX L A mem md p n i HM Hin Hi) as Hni.
        exact (Hni (caw_errno_img _ He)).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  split; [exact HWF|]. split; [exact HBD|]. split; [exact HLY|]. split; [exact HI|].
  split.
  { intros Hf i Hi. rewrite <- (HLB Hf i Hi).
    assert (Ho : owned B L A (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
    destruct (OWN _ Ho) as [Hl0 Hout]. apply (mbyte_munch _ W); [exact MU | lia | exact Hout]. }
  split; [exact HLN|]. split; [exact HUB|]. split; [exact HMD|].
  split.
  { intros a Ha Hsc. destruct (HHI a Ha Hsc) as [E1 E2].
    assert (Hout : Frame.outside W a).
    { apply OUT; [lia | intros H; apply Hsc; left; exact H | intros H; apply Hsc; right; exact H |].
      intros r k Hr _ Hrx. pose proof (caw_block_range L A mem md r k HM Hr). lia. }
    split; [rewrite (mbyte_munch _ W mem mem' a MU ltac:(lia) Hout); exact E1|].
    rewrite E2. apply (writable_munch _ W mem mem' a MU ltac:(lia) Hout). }
  split.
  { intros a Ha Hno Hsc. destruct (HIM a Ha Hno Hsc) as [E1 E2].
    pose proof (proj1 caw_img_low a Ha) as Hal.
    assert (Hout : Frame.outside W a).
    { apply OUT; [lia | intros H; apply Hsc; left; exact H | intros H; apply Hsc; right; exact H |].
      intros r k Hr _ Hrx.
      destruct (caw_block_facts L A mem md r k (a - r) HM Hr ltac:(lia)) as (_ & _ & _ & _ & Hni).
      replace (r + (a - r)) with a in Hni by lia. exact (Hni Ha). }
    split; [rewrite (mbyte_munch _ W mem mem' a MU ltac:(lia) Hout); exact E1|].
    rewrite E2. apply (writable_munch _ W mem mem' a MU ltac:(lia) Hout). }
  split.
  { intros p n i Hin Hi. rewrite <- (HB0 p n i Hin Hi).
    destruct (HUB p n Hin) as [HinA Hptr].
    pose proof (caw_ub_blocks L A p n HinA) as HinB. rewrite Hptr in HinB.
    destruct (caw_block_facts L A mem md _ n i HM HinB Hi) as (_ & H4 & Hc & _ & Hni).
    assert (Hout : Frame.outside W (ptr_addr L0 p + i)).
    { apply OUT; [lia | lia | intros He; exact (Hni (caw_errno_img _ He)) |]. intros r k Hr Hr0 Hrx.
      assert (Hne : (ptr_addr L0 p, n) <> (r, k)).
      { intros E. apply Hr0. rewrite <- E. apply caw_ub_blocks. exact Hin. }
      destruct (caw_blocks_sep L A mem md _ _ HM HinB Hr Hne) as [D|D]; cbn [fst snd] in D; lia. }
    apply (mbyte_munch _ W); [exact MU | lia | exact Hout]. }
  split; [intros a Hs; apply WM; apply HSC; exact Hs|].
  exact RA'.
Qed.

Lemma caw_layout_trans : forall L A L', layout_le A0 L0 L -> layout_le A L L' ->
  (length (st_regions A0) <= length (st_regions A))%nat -> layout_le A0 L0 L'.
Proof.
  intros L A L' (E1 & E2 & E3 & E4) (F1 & F2 & F3 & F4) Hl.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite F4 by lia. apply E4. exact Hr.
Qed.

Lemma cj_callpost : forall L A mem md Kc regs_c Ec L' A' regs' mem' md',
  cj L A mem md -> call_post_k B MR Kc L A regs_c mem md Ec L' A' regs' mem' md' ->
  spZ regs0 - CAW_K <= spZ regs_c - Kc -> spZ regs_c <= spZ regs0 ->
  (forall a, Ec a -> a < alloc_ceiling /\ ~ in_img B a /\
     forall p n, In (p, n) (user_blocks A0) -> ~ (ptr_addr L0 p <= a < ptr_addr L0 p + n)) ->
  (forall p n, In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A')) ->
  st_init_done A' = true ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  ro_agree segs mem' ->
  cj L' A' mem' md'.
Proof using PRE0.
  intros L A mem md Kc regs_c Ec L' A' regs' mem' md' J CP Hk1 Hk2 HE HSURV HINIT HLEN RA'.
  pose proof J as (HM & HWF & HBD & HLY & HI & HLB & HLN & HUB & (vm & HMD) & HHI & HIM & HB0 & HSC & HRA).
  destruct CP as (HM' & HWF' & HBD' & HLY' & HPTR & _ & (vm' & HMD') & HFR & HBK & HSC').
  pose proof PRE0 as (HM0 & _ & _ & _ & _ & HK & HK63 & _). pose proof caw_k_val as HKv.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hac. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as Hacv.
  assert (NSC : forall a, ~ scratch_k B CAW_K regs0 a -> ~ scratch_k B Kc regs_c a).
  { intros a H1 H2. apply H1. unfold scratch_k in *. destruct H2 as [H2|H2]; [left; lia | right; exact H2]. }
  split; [exact HM'|]. split; [exact HWF'|]. split; [exact HBD'|].
  split; [exact (caw_layout_trans L A L' HLY HLY' HLN)|].
  split; [intros _; exact HINIT|].
  split; [intros H; congruence|].
  split; [lia|].
  split.
  { intros p n Hp. destruct (HUB p n Hp) as [HA Hptr]. split; [exact (HSURV p n Hp)|].
    rewrite (HPTR p n HA (HSURV p n Hp)). exact Hptr. }
  split; [exists vm'; rewrite HMD', HMD; apply caw_vm_twice|].
  split.
  { intros a Ha Hsc. destruct (HHI a Ha Hsc) as [E1 E2].
    destruct (HFR a (or_introl Ha)) as [F1 F2].
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
    - exact (NSC a Hsc).
    - intros He. destruct (HE a He). lia.
    - split; [rewrite F1; exact E1 | rewrite E2; exact F2]. }
  split.
  { intros a Ha Hno Hsc. destruct (HIM a Ha Hno Hsc) as [E1 E2].
    destruct (HFR a (or_intror Ha)) as [F1 F2].
    - exact (Hno L A mem md HM).
    - exact (Hno L' A' mem' md' HM').
    - exact (NSC a Hsc).
    - intros He. destruct (HE a He) as (_ & Hn & _). exact (Hn Ha).
    - split; [rewrite F1; exact E1 | rewrite E2; exact F2]. }
  split.
  { intros p n i Hp Hi. destruct (HUB p n Hp) as [HA Hptr]. rewrite <- Hptr.
    rewrite (HBK p n i HA (HSURV p n Hp) Hi). rewrite Hptr. exact (HB0 p n i Hp Hi). }
  split.
  { intros a Hs.
    assert (D : scratch_k B Kc regs_c a \/ ~ scratch_k B Kc regs_c a).
    { unfold scratch_k. destruct (Z_le_gt_dec (spZ regs_c - Kc) a); destruct (Z_lt_ge_dec a (spZ regs_c));
        destruct (Z_le_gt_dec (errno_addr B) a); destruct (Z_lt_ge_dec a (errno_addr B + 4));
        first [left; lia | right; lia]. }
    destruct D as [D|D]; [exact (HSC' a D)|].
    destruct Hs as [Hs|Hs]; [|exfalso; apply D; right; exact Hs].
    assert (Hhi : alloc_ceiling <= a < 2 ^ 64) by lia.
    destruct (HFR a (or_introl Hhi)) as [_ F2].
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
    - exact D.
    - intros He. destruct (HE a He). lia.
    - apply F2. apply HSC. left. exact Hs. }
  exact RA'.
Qed.

End G.
